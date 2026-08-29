"""Two-model coordination agent: escalating ladder with cross-model interfaces.

Stages (design and evidence in RESEARCH.md §6):
  S0  deterministic tactic sweep (zero LLM cost)
  S1  pooled diverse whole-proof sampling from both models
  S2  capped compiler-feedback repair on nearest misses
  S3  plateau-triggered cross-model handoff (inside the repair loop)
  S4  sketch/fill decomposition with a per-problem proven-lemma pool
  S5  finalize: re-verify best, guard, checkpoint, return

Safety rails (harness mechanics, RESEARCH.md §1):
  - self-managed soft deadline: the worker's cancel mid-LLM-call zeroes the
    problem, so no call may outlive our own clock;
  - one transport error closes the budget ledger for good: LLM failures
    degrade to LLM-free mode instead of retrying;
  - statements are never editable: S0/S4 splice into pristine text, model
    files are checked against pristine signatures;
  - sorry/admit/native_decide/axiom are lexically banned from final output;
  - numeric answers are normalized to decimal literals.

Environment knobs (defaults are the submission configuration):
  SUBMISSION_MODELS         duo | qwen | gptoss   (part-2 arms; default duo)
  SUBMISSION_DISABLE_LLM    1 to run S0 only
  SUBMISSION_QWEN_SAMPLES   S1 samples from qwen (default 8)
  SUBMISSION_GPTOSS_SAMPLES S1 samples from gpt-oss (default 2)
  SUBMISSION_REPAIR_ROUNDS  repair rounds per candidate incl. handoff (default 4)
  SUBMISSION_SKETCH_ROUNDS  S4 sketch attempts (default 4)
"""

from __future__ import annotations

import asyncio
import difflib
import hashlib
import json
import os
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable

from re_harness import AgentResult, Problem, Services
from re_harness.budget import BudgetAccountingError, BudgetExceeded
from re_harness.lean import LeanRuntimeError
from re_harness.llm import LLMCallError, LLMPolicyError
from re_harness.models import MODEL_A as QWEN, MODEL_B as GPTOSS

from submission.lean_text import (
    Parsed,
    axiom_violations,
    bounded_intro_templates,
    classify_goal,
    error_signature,
    extract_lean,
    format_messages,
    guard_candidate,
    insert_preamble,
    parse_challenge,
    splice_holes,
    splice_tactics,
)

# ---------------------------------------------------------------------------
# Configuration


def _env_int(name: str, default: int, lo: int, hi: int) -> int:
    raw = os.environ.get(name, "").strip()
    if not raw:
        return default
    try:
        return min(hi, max(lo, int(raw)))
    except ValueError:
        return default


@dataclass(frozen=True)
class Config:
    time_limit_s: float
    verify_reserve_s: float
    models: str
    disable_llm: bool
    qwen_samples: int
    gptoss_samples: int
    repair_rounds: int
    sketch_rounds: int
    gptoss_call_cap: int

    # Worst-case single-call wall clock (observed: gpt-oss ~8 min on hard prompts).
    qwen_call_s: float = 300.0
    gptoss_call_s: float = 960.0
    llm_concurrency: int = 3
    shortcap: bool = False
    fill_breadth: bool = False
    fill_reasoning: bool = False
    skeleton_keep: bool = False
    skeleton_portfolio: bool = False
    compare_precheck: bool = True
    bound_templates: bool = False
    plan_first: bool = False
    # SUBMISSION_WAVE_SPREAD (research branch B1): S1 qwen-fast temperature
    # cycling + short-window wave growth; default off.
    # SUBMISSION_TYPED_FILLS (research branch B4): goal-class-specific
    # technique block appended to S4 fill dialogues; default off.
    typed_fills: bool = False
    # SUBMISSION_STRENGTHEN_IH (research branch B7): re-sketch notes tell the
    # sketcher to STRENGTHEN repeatedly-unfilled induction-shaped helpers
    # instead of only shrinking them; default off.
    strengthen_ih: bool = False
    # SUBMISSION_CRITIC_NOTES (research branch B8): after a repair pass that
    # closed nothing, one bounded gpt-oss diagnosis of the best near-miss is
    # appended to history_notes for later S1 waves. A hint, never a judge
    # (RESEARCH.md §4.2); default off.
    critic_notes: bool = False
    suggest_harvest: bool = False
    wave_spread: bool = False
    # SUBMISSION_PREMISE_HINTS (research branch B5): REPL-verified Mathlib
    # premise names injected into S4 fill prompts; default off.
    premise_hints: bool = False
    # SUBMISSION_CLUSTER_REPAIR (research branch B3): S2 groups near-misses by
    # error fingerprint, repairs one representative per cluster, and replays
    # an accepted fix textually on the siblings (no LLM calls); default off.
    cluster_repair: bool = False

    @classmethod
    def from_env(cls) -> "Config":
        limit = float(os.environ.get("VM_TIME_LIMIT_S", "28800") or 28800)
        reserve = float(os.environ.get("VM_VERIFY_RESERVE_S", "120") or 120)
        return cls(
            time_limit_s=limit,
            verify_reserve_s=reserve,
            models=os.environ.get("SUBMISSION_MODELS", "duo").strip() or "duo",
            disable_llm=os.environ.get("SUBMISSION_DISABLE_LLM", "").strip() == "1",
            qwen_samples=_env_int("SUBMISSION_QWEN_SAMPLES", 8, 0, 64),
            gptoss_samples=_env_int("SUBMISSION_GPTOSS_SAMPLES", 2, 0, 64),
            repair_rounds=_env_int("SUBMISSION_REPAIR_ROUNDS", 4, 0, 12),
            sketch_rounds=_env_int("SUBMISSION_SKETCH_ROUNDS", 4, 0, 12),
            gptoss_call_cap=_env_int("SUBMISSION_GPTOSS_CALL_CAP", 10, 0, 200),
            # Promoted default (RESEARCH_LOOP.md iter-2); "0" restores the
            # fixed long-window constants.
            shortcap=os.environ.get("SUBMISSION_SHORTCAP", "1").strip() != "0",
            # Research branch B9: two-slot portfolio of distinct partial
            # skeletons resumed on alternating S4 rounds; default off.
            skeleton_portfolio=os.environ.get(
                "SUBMISSION_SKELETON_PORTFOLIO", "").strip() == "1",
            # SUBMISSION_TYPED_FILLS (research branch B4): default off.
            typed_fills=os.environ.get("SUBMISSION_TYPED_FILLS", "").strip() == "1",
            # Promoted default (RESEARCH_LOOP.md iter-3); "0" restores
            # depth-first-only fills.
            fill_breadth=os.environ.get("SUBMISSION_FILL_BREADTH", "1").strip() != "0",
            fill_reasoning=os.environ.get("SUBMISSION_FILL_REASONING", "").strip() == "1",
            # SUBMISSION_STRENGTHEN_IH (research branch B7): default off.
            strengthen_ih=os.environ.get(
                "SUBMISSION_STRENGTHEN_IH", "").strip() == "1",
            skeleton_keep=os.environ.get("SUBMISSION_SKELETON_KEEP", "").strip() == "1",
            # B10 (default off): deterministic intro + interval_cases
            # templates for bounded-∀ statements, tried before FILL_SWEEP.
            bound_templates=os.environ.get(
                "SUBMISSION_BOUND_TEMPLATES", "").strip() == "1",
            # SUBMISSION_CRITIC_NOTES (research branch B8): default off.
            critic_notes=os.environ.get("SUBMISSION_CRITIC_NOTES", "").strip() == "1",
            # Default on: three p10 proofs were REPL-accepted yet timed out
            # B6 (default off): per-hole `apply?` Try-this harvesting in S4 fills.
            suggest_harvest=os.environ.get(
                "SUBMISSION_SUGGEST_HARVEST", "").strip() == "1",
            # Research branch B2 (DSP-lite): majority-pick an informal plan
            # before the cycle-1 S1 wave and condition qwen-fast samples on it.
            plan_first=os.environ.get("SUBMISSION_PLAN_FIRST", "").strip() == "1",
            # the comparator's cold build — only the real gate can see that.
            compare_precheck=os.environ.get(
                "SUBMISSION_COMPARE_PRECHECK", "1").strip() != "0",
            # SUBMISSION_WAVE_SPREAD (research branch B1): default off.
            wave_spread=os.environ.get("SUBMISSION_WAVE_SPREAD", "").strip() == "1",
            # SUBMISSION_PREMISE_HINTS (research branch B5): default off.
            premise_hints=os.environ.get(
                "SUBMISSION_PREMISE_HINTS", "").strip() == "1",
            # SUBMISSION_CLUSTER_REPAIR (research branch B3): default off.
            cluster_repair=os.environ.get("SUBMISSION_CLUSTER_REPAIR", "").strip() == "1",
        )

    @property
    def agent_time_s(self) -> float:
        # Mirror worker.py: agent gets time_limit - min(reserve, 25% of limit).
        return max(1.0, self.time_limit_s - min(self.verify_reserve_s, self.time_limit_s * 0.25))

    @property
    def margin_s(self) -> float:
        return min(600.0, max(20.0, self.agent_time_s * 0.12))

    def scaled(self, seconds: float) -> float:
        """Window-proportional time constant (SUBMISSION_SHORTCAP variant).

        The default constants assume long windows; below a ~40-minute agent
        window they saturate the guards — a 960 s gpt-oss timeout can never
        fit a 1080 s window, and S4's 900 s entry gate never opens — which
        silently disables the gpt-oss channel and decomposition at short
        caps (measured: iter-0 baseline, RESEARCH_LOOP.md). Scaling by
        agent_time/2400 restores every stage there; at 40+ minute windows
        this is the identity, so judge-cap behavior is unchanged.
        """
        if not self.shortcap:
            return seconds
        return max(60.0, seconds * min(1.0, self.agent_time_s / 2400.0))

    def other(self, model: str) -> str:
        if self.models == "qwen":
            return QWEN
        if self.models == "gptoss":
            return GPTOSS
        return GPTOSS if model == QWEN else QWEN


# ---------------------------------------------------------------------------
# SUBMISSION_WAVE_SPREAD (research branch B1): S1 qwen-fast temperature cycle

WAVE_SPREAD_TEMPS: tuple[float, ...] = (0.5, 0.8, 1.1)


def wave_spread_temperature(index: int) -> float:
    """Temperature for the index-th qwen-fast sample of an S1 wave.

    Cycling conservative/default/adventurous decoding decorrelates a wave
    that n draws at a fixed t=0.8 leave clustered — the dev-set flippers
    (c03/m01/h05, RESEARCH_LOOP.md) flip pass/fail on exactly that S1
    sampling luck.
    """
    return WAVE_SPREAD_TEMPS[index % len(WAVE_SPREAD_TEMPS)]


# ---------------------------------------------------------------------------
# SUBMISSION_STRENGTHEN_IH (research branch B7): induction-hole triage

STRENGTHEN_IH_TEXT = (
    "For {name}: the induction hypothesis as stated appears too weak — "
    "restate the helper with a STRONGER induction hypothesis (more general "
    "n, an explicit bound, or a conjunction capturing the needed "
    "invariant), then derive the original.")


def induction_like(decl_statement: str) -> bool:
    """Cheap pure predicate: does this statement look induction-shaped?

    Textual only, no elaboration: a `∀` binder ascribed over ℕ/Nat, or an
    operator whose goals usually fall to induction — `Finset.sum` /
    `Finset.prod` (including their `∑`/`∏` notations, which signatures
    preserve), `^`, or factorial `!`. A false positive merely adds one
    advice line to a re-sketch note.
    """

    import re as _re
    if _re.search(r"∀[^,]*:\s*(?:ℕ|Nat(?![A-Za-z0-9_'.]))", decl_statement):
        return True
    return bool(_re.search(r"Finset\.(?:sum|prod)|[∑∏^!]", decl_statement))


def strengthen_ih_note(tb: Toolbox, source: str) -> str:
    """Flag-guarded addendum for stage4's re-sketch note ("" when off).

    Measured failure family (m01/h03 class): induction holes fail
    repeatedly because the stated induction hypothesis is too weak, yet the
    generic note asks for SMALLER lemmas — the opposite of the hand-proof
    fix, which strengthens the statement being inducted on. For each decl
    still unfilled after >= 2 failed fill dialogues whose statement is
    induction_like, append an explicit strengthen-the-IH instruction.
    """

    if not tb.config.strengthen_ih:
        return ""
    import re as _re
    signatures = parse_challenge(source).signatures
    picked: list[str] = []
    for name in tb.last_unfilled:
        if tb.fill_failures.get(name, 0) < 2:
            continue
        statement = next(
            (s for s in signatures
             if _re.match(rf"\S+\s+{_re.escape(name)}(?![A-Za-z0-9_'.])", s)),
            "")
        if induction_like(statement):
            picked.append(name)
    if not picked:
        return ""
    tb.log(stage="S4", strengthen_ih=picked)
    return "".join("\n" + STRENGTHEN_IH_TEXT.format(name=name) for name in picked)


# ---------------------------------------------------------------------------
# Prompt material (generic technique guidance only — no per-problem content)

COOKBOOK = """Lean 4 / current Mathlib technique notes:
- ℕ subtraction truncates: prefer `omega` for linear goals; `zify [h]` with the
  needed `≤` side conditions to move to ℤ, and `push_cast` after `subst`.
- Modular arithmetic cycles: `conv_lhs => rw [← Nat.div_add_mod n k, pow_add,
  pow_mul]` then `Nat.mul_mod, Nat.pow_mod` and finish by cases on `n % k`
  with `omega`.
- `∀ n ≥ k` goals: `induction n, hn using Nat.le_induction`.
- Finite checks: derive bounds first (e.g. `a ≤ a * b` when `0 < b`), then
  `interval_cases a <;> omega` or `<;> decide`.
- Heavy computation: add `set_option maxHeartbeats 1000000`,
  `set_option exponentiation.threshold 10000`, `set_option maxRecDepth 8000`
  above the theorem. `decide` is allowed; `native_decide` is FORBIDDEN.
- Cancel factors with `Nat.eq_of_mul_eq_mul_left` after
  `rw [show A = B by ring]`; bound divisors with `Int.le_of_dvd`.
- Useful closers: omega, norm_num [...], nlinarith [sq_nonneg (a-b), ...],
  positivity, field_simp; ring, aesop, simp_all.
- `gcongr` proves monotonicity goals (sums, products, divisions) in one step
  and discharges side conditions itself — prefer it over hunting for
  div_le_div-style lemma names. `Finset.sum_le_card_nsmul` bounds a sum by
  card • bound; `Finset.sum_Ico_consecutive` splits ranges.
- This Mathlib deprecates `push_neg` (warning only); `by_contra h` then `push_neg at h`
  still works, or use `omega`-friendly reformulations.
- If an identifier was reported unknown, it DOES NOT EXIST in this Mathlib —
  never use it again; reach the fact another way (different lemma, omega,
  explicit have-chain). Pay attention to mistakes already made and avoid
  repeating them; when the same error resists two fixes, change approach
  entirely rather than patching again."""

RULES_BLOCK = """Hard rules:
- Return ONE complete Lean file in a single ```lean code block.
- Keep every theorem/abbrev statement byte-for-byte identical to the challenge;
  you may add helper lemmas ABOVE the theorems.
- Never use admit, axiom, native_decide, or Lean 3 syntax.
- Numeric answer abbrevs (`abbrev … : ℕ :=`) must be plain decimal literals."""

# SUBMISSION_TYPED_FILLS (research branch B4): per-goal-class technique blocks
# appended to S4 fill dialogues. Keys match lean_text.classify_goal; generic
# Mathlib guidance only — no problem-specific content.
FILL_TECHNIQUES: dict[str, str] = {
    "induction": """Goal-class hints (induction):
- `induction n` for goals from 0; `induction n, hn using Nat.le_induction` for `∀ n ≥ k`; `Nat.strong_induction_on` for two-step recurrences.
- If the induction hypothesis is too weak, strengthen it: prove a sharper auxiliary claim (`suffices` or a helper `have` generalizing the statement) and specialize.
- Unfold one step via `Finset.sum_range_succ`/`Finset.prod_range_succ`/`Nat.factorial_succ`, then close the step with `ring_nf`, `omega`, or `nlinarith` fed the IH.
- Discharge the base case separately with `norm_num` or `decide`.""",
    "divisibility": """Goal-class hints (divisibility):
- Build `∣` facts by chaining `dvd_mul_of_dvd_left/right`, `dvd_add`, `Nat.dvd_sub'`, and `Dvd.dvd.trans`.
- `Nat.Prime.dvd_mul` splits `p ∣ a * b`; `Nat.Prime.coprime_iff_not_dvd` and `Nat.Coprime.dvd_of_dvd_mul_left/right` exploit coprimality.
- For gcd goals use `Nat.dvd_gcd` and `Nat.gcd_dvd_left/right`; `Nat.Coprime` unfolds to `gcd = 1`.
- `Nat.dvd_iff_mod_eq_zero` links `∣` to `%`; on concrete moduli, case-split on the residue and finish with `omega` or `decide`.""",
    "inequality": """Goal-class hints (inequality):
- Try `omega` (linear ℕ/ℤ) and `positivity` (`0 < e`, `0 ≤ e`, `e ≠ 0`) first; `gcongr` closes monotonicity goals (sums, products, powers, divisions) and discharges side conditions itself.
- `nlinarith` needs hints for products and squares: pass facts like `[sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb]`.
- Chain estimates with `calc` plus `le_trans`/`lt_of_le_of_lt`/`lt_of_lt_of_le`.
- Clear denominators before comparing: `div_le_iff`/`le_div_iff` (positivity side goals) or `field_simp`.""",
    "cast": """Goal-class hints (mixed ℕ/ℤ/ℝ casts):
- Pick the widest type once: `zify [h₁, …]` (supplying the `≤` facts ℕ-subtraction needs) or `rify`, then stay there.
- `push_cast` pushes `↑` inward through `+ * ^`; `norm_cast` collapses a goal that is really single-type; `exact_mod_cast h` transports hypotheses across casts.
- Lemma-level moves: `Nat.cast_le`, `Nat.cast_lt`, `Nat.cast_inj`, `Int.toNat_of_nonneg`.
- Rewrite ℕ subtraction/division away first (`Nat.sub_add_cancel`, `Nat.div_mul_cancel` under the right hypotheses) — casts do not commute with truncating operations.""",
    "arith": """Goal-class hints (arithmetic/computation):
- `omega` decides linear ℕ/ℤ goals including `%` and `/` by constants — try it first; `decide` settles small closed decidable facts (`native_decide` is forbidden).
- `norm_num` evaluates numeric (in)equalities; extend it as `norm_num [lemma₁, …]` when definitions block it.
- `ring`/`ring_nf` proves commutative-(semi)ring identities; `simp [...]` to normalize, then finish with `omega`/`norm_num`.
- If a computation times out, shrink it first (`Nat.pow_mod`, `set_option maxHeartbeats 1000000` above the theorem) before retrying `decide`.""",
}


def whole_proof_messages(problem: Problem, challenge: str, feedback: str = "",
                         history: str = "", plan: str = "") -> list[dict[str, str]]:
    system = (
        "You are an expert Lean 4 / Mathlib prover. Produce a complete, compiling "
        "Lean file that proves the challenge theorem(s), replacing every `sorry`.\n"
        + RULES_BLOCK + "\n- Do not use sorry.\n\n" + COOKBOOK
    )
    user = [
        f"Problem {problem.id}:", problem.description, "",
        "Challenge file (fill in the sorries, change nothing else):",
        "```lean", challenge.rstrip(), "```",
    ]
    if plan:  # SUBMISSION_PLAN_FIRST: condition the wave on a shared strategy.
        user = ["A promising strategy:", plan,
                "Follow it unless clearly wrong.", ""] + user
    if history:
        user += ["", "What has been tried so far (do something different):", history]
    if feedback:
        user += ["", "Lean compiler feedback on the previous attempt:",
                 "```", feedback, "```",
                 "Fix the reported problems. Return the full corrected file."]
    return [{"role": "system", "content": system},
            {"role": "user", "content": "\n".join(user)}]


def plan_messages(problem: Problem, challenge: str) -> list[dict[str, str]]:
    """Compact plan prompt (SUBMISSION_PLAN_FIRST): idea + strategy, no Lean."""

    system = (
        "You are an expert competition mathematician planning a Lean 4 proof. "
        "Answer in at most 6 short lines: the key mathematical idea and the "
        "proof strategy. Plain text only; no Lean code."
    )
    user = [
        f"Problem {problem.id}:", problem.description, "",
        "Challenge file:", "```lean", challenge.rstrip(), "```", "",
        "In <=6 lines: the key mathematical idea and proof strategy; "
        "no Lean code.",
    ]
    return [{"role": "system", "content": system},
            {"role": "user", "content": "\n".join(user)}]


def pick_plan(plans: list[str] | None) -> str | None:
    """Majority-pick one informal plan (SUBMISSION_PLAN_FIRST; pure).

    Each plan is normalized to a crude strategy key: its first non-empty
    line, lowercased, punctuation stripped, whitespace collapsed. If two
    plans share a key, the first of them wins; otherwise the longest plan
    wins. None, empty, or all-blank input yields None.
    """

    usable = [p.strip() for p in (plans or [])
              if isinstance(p, str) and p.strip()]
    if not usable:
        return None

    def key(plan: str) -> str:
        first = plan.splitlines()[0].lower()
        cleaned = "".join(c if c.isalnum() or c.isspace() else " " for c in first)
        return " ".join(cleaned.split())

    keys = [key(p) for p in usable]
    for i, k in enumerate(keys):
        if k and k in keys[i + 1:]:
            return usable[i]
    return max(usable, key=len)


def critic_messages(problem: Problem, source: str,
                    feedback: str) -> list[dict[str, str]]:
    """Bounded diagnosis prompt (SUBMISSION_CRITIC_NOTES): root cause, no code."""

    system = (
        "You are an expert Lean 4 / Mathlib prover reviewing a failed proof "
        "attempt. Answer in at most 8 short lines of plain text. NO Lean code."
    )
    user = [
        f"Problem {problem.id}:", problem.description, "",
        "Best failed attempt:", "```lean", source[:6000], "```", "",
        "Lean compiler feedback:", "```", feedback, "```", "",
        "In <=8 lines: diagnose the mathematical/technical root cause and "
        "state a concrete alternative approach. NO Lean code.",
    ]
    return [{"role": "system", "content": system},
            {"role": "user", "content": "\n".join(user)}]


def sketch_messages(problem: Problem, challenge: str, lemma_pool: str,
                    prior_note: str = "") -> list[dict[str, str]]:
    system = (
        "You are an expert Lean 4 / Mathlib prover planning a difficult proof by "
        "decomposition. Write a PROOF SKELETON: a complete Lean file where\n"
        "- prefer MANY SMALL lemmas over few large ones: every helper must be "
        "individually easy to prove (one induction, one case split, one "
        "computation each),\n"
        "- helper lemmas are fully STATED with `:= by sorry` bodies (choose helper "
        "statements that are individually easy to prove and together imply the goal),\n"
        "- the main theorem(s) are proved USING those helpers, with `sorry` only "
        "where genuinely unavoidable,\n"
        "- every helper you state must be precise and true.\n"
        + RULES_BLOCK + "\n\n" + COOKBOOK
    )
    user = [
        f"Problem {problem.id}:", problem.description, "",
        "Challenge file (keep these statements exactly; add helpers above):",
        "```lean", challenge.rstrip(), "```",
    ]
    if lemma_pool:
        user += ["", "Already-proven helper lemmas you may reuse verbatim "
                 "(include them in your file with their proofs):",
                 "```lean", lemma_pool, "```"]
    if prior_note:
        user += ["", "Notes from previous attempts:", prior_note]
    return [{"role": "system", "content": system},
            {"role": "user", "content": "\n".join(user)}]


def fill_messages(problem: Problem, sketch: str, decl_name: str,
                  feedback: str = "", hints: str = "",
                  technique: str = "") -> list[dict[str, str]]:
    system = (
        "You are an expert Lean 4 / Mathlib prover. The file below compiles except "
        "for `sorry` placeholders. Your job is ONE hole: the `sorry` inside the "
        f"declaration `{decl_name}`.\n"
        "Respond with up to THREE genuinely different candidate proofs for that "
        "hole. Each candidate is its own ```lean code block containing ONLY the "
        "tactic script that replaces the `sorry` (no theorem header, no imports; "
        "`have`/`calc` inside the script are fine). Order them most-likely-first "
        "and make them structurally different (different tactics or proof idea, "
        "not cosmetic variants).\n"
        "Never use sorry, admit, axiom, or native_decide.\n\n" + COOKBOOK
    )
    user = [
        f"Problem {problem.id} — current file:",
        "```lean", sketch.rstrip(), "```",
        "",
        f"Give up to three alternative proofs for the `sorry` in `{decl_name}`, "
        "each in its own ```lean block.",
    ]
    if hints:
        user += ["", hints]
    if feedback:
        user += ["", "Lean feedback on the previous attempt at this hole:",
                 "```", feedback, "```"]
    if technique:  # SUBMISSION_TYPED_FILLS (B4): goal-class-specific guidance.
        user += ["", technique]
    return [{"role": "system", "content": system},
            {"role": "user", "content": "\n".join(user)}]


def answer_messages(problem: Problem, challenge: str, names: list[str],
                    disagreement: str = "") -> list[dict[str, str]]:
    answer_lines = "\n".join(f"ANSWER {name}: <integer or arithmetic expression>"
                             for name in names)
    system = (
        "You are a careful competition mathematician. Determine the numeric "
        "value(s) the problem asks for. Reason step by step, sanity-check with "
        "small cases or modular arithmetic, then end your reply with exactly:\n"
        f"{answer_lines}\n"
        "Expressions may use only integers and + - * / % ^ ( ). No words on "
        "those final lines."
    )
    user = [
        f"Problem {problem.id}:", problem.description, "",
        "Formal statement for reference:", "```lean", challenge.rstrip(), "```",
    ]
    if disagreement:
        user += ["", "Two independent derivations disagreed:", disagreement,
                 "Find the error and give the correct final answer."]
    return [{"role": "system", "content": system},
            {"role": "user", "content": "\n".join(user)}]


def parse_answer_lines(text: str, names: list[str]) -> dict[str, int] | None:
    """Extract `ANSWER name: expr` lines; single-name problems may omit the name."""

    import re as _re
    from submission.lean_text import eval_nat_literal
    found: dict[str, int] = {}
    for match in _re.finditer(
            r"^\s*ANSWER(?:\s+([A-Za-z0-9_'.]+))?\s*[:=]\s*(.+?)\s*$",
            text or "", _re.MULTILINE):
        name = match.group(1) or (names[0] if len(names) == 1 else None)
        if name not in names:
            continue
        value = eval_nat_literal(match.group(2))
        if value is not None:
            found[name] = value
    return found if len(found) == len(names) else None


# ---------------------------------------------------------------------------
# Premise hints (SUBMISSION_PREMISE_HINTS / B5): hallucinated Mathlib names
# ("unknown identifier") are a top fill-error class. One cheap call proposes
# candidate lemma names, one batched `#check` file verifies which exist —
# `#check <name>` errors iff the name is unknown — and only survivors are
# ever injected into fill prompts.


def premise_messages(problem: Problem, challenge: str) -> list[dict[str, str]]:
    system = (
        "You are a Lean 4 / Mathlib librarian. List Mathlib lemma or theorem "
        "names likely to be useful for proving the problem below.\n"
        "Rules: at most 15 names, fully qualified (e.g. `Nat.pow_mod`, "
        "`Finset.sum_range_succ`), ONE name per line, no code, no commentary."
    )
    user = [
        f"Problem {problem.id}:", problem.description, "",
        "Formal statement:", "```lean", challenge.rstrip(), "```", "",
        "List up to 15 likely-relevant Mathlib lemma names, one per line.",
    ]
    return [{"role": "system", "content": system},
            {"role": "user", "content": "\n".join(user)}]


def parse_premise_names(text: str, cap: int = 15) -> list[str]:
    """Qualified identifiers (`Nat.pow_mod`) from LLM output, deduped, capped."""

    import re as _re
    names: list[str] = []
    for match in _re.finditer(
            r"\b[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+", text or ""):
        name = match.group(0)
        if all(len(segment) <= 1 for segment in name.split(".")):
            continue  # prose artifacts like `e.g` / `i.e`
        if name not in names:
            names.append(name)
        if len(names) >= cap:
            break
    return names


def failed_premise_indexes(messages: list[dict[str, Any]], count: int) -> set[int]:
    """0-based indexes of `#check` candidates whose line carries an error.

    Mirrors _sorrify_progress's accounting: the REPL strips import lines, so
    message line numbers are 1-based over the KEPT lines — and the premise
    probe file is imports followed immediately by one `#check` per candidate,
    so kept line k is candidate k-1. An error that cannot be attributed to a
    candidate line fails the whole batch (never inject unvetted names).
    """

    failed: set[int] = set()
    for message in messages:
        if message.get("severity") != "error":
            continue
        line = (message.get("pos") or {}).get("line")
        if isinstance(line, int) and 1 <= line <= count:
            failed.add(line - 1)
        else:
            return set(range(count))
    return failed


# ---------------------------------------------------------------------------
# Deterministic sweep (S0) — generic tactic cocktail, cheap-to-expensive

OPTIONS_PREAMBLE = (
    "set_option maxHeartbeats 1000000\n"
    "set_option maxRecDepth 8000\n"
    "set_option exponentiation.threshold 10000"
)

SWEEP: list[tuple[str, str]] = [
    ("linarith", ""),
    ("norm_num", ""),
    ("rfl", ""),
    ("omega", ""),
    ("simp", ""),
    ("simp_all", ""),
    ("ring", ""),
    ("positivity", ""),
    ("subst h\nnorm_num", ""),
    ("field_simp\nring", ""),
    ("nlinarith", ""),
    ("nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]", ""),
    ("nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]", ""),
    ("constructor <;> norm_num", ""),
    ("norm_num [Nat.factorial]", ""),
    ("norm_num [Nat.dvd_iff_mod_eq_zero]", ""),
    ("aesop", ""),
    ("decide", ""),
    ("decide", OPTIONS_PREAMBLE),
    ("norm_num", OPTIONS_PREAMBLE),
    ("simp_all\nomega", ""),
    ("exact?", ""),
]

# Shorter cascade used on individual S4 holes before any LLM call.
FILL_SWEEP = ["linarith", "norm_num", "omega", "simp", "simp_all", "positivity",
              "nlinarith", "ring", "aesop", "norm_num [Nat.factorial]", "decide",
              "try norm_cast\ntry norm_num\ntry simp_all\nnlinarith",
              "try push_cast\ntry field_simp\ntry ring_nf\nnlinarith",
              # Mined against archived failed holes (RESEARCH_LOOP.md,
              # 2026-08-26): the first two close the recurring
              # modular-power/induction-step family; nothing above touched
              # those goals.
              "try intros\ntry simp only [pow_succ, pow_add, pow_mul, "
              "pow_zero, pow_one] at *\nomega",
              "try intros\nsimp [pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod]",
              "simp [Nat.sq_sub_sq, Nat.mul_comm]",
              "exact?"]

TRY_THIS = "Try this:"


def harvest_try_this(messages: list[dict[str, Any]]) -> list[str]:
    """Cleaned `Try this:` suggestions from REPL messages, deduped, in order.

    Pure and offline-testable. Used by the SUBMISSION_SUGGEST_HARVEST per-hole
    `apply?` probe in S4 fills — distinct from S0's `_concretize_exact`, which
    re-splices a whole-file `exact?` that already closed every hole.
    """

    seen: set[str] = set()
    suggestions: list[str] = []
    for message in messages:
        data = str(message.get("data", ""))
        for chunk in data.split(TRY_THIS)[1:]:
            suggestion = chunk.strip()
            if suggestion and suggestion not in seen:
                seen.add(suggestion)
                suggestions.append(suggestion)
    return suggestions


# ---------------------------------------------------------------------------
# Bookkeeping


@dataclass
class Candidate:
    source: str
    origin: str
    accepted: bool = False
    error_count: int = 10**6
    sorry_count: int = 0
    messages: list[dict[str, Any]] = field(default_factory=list)
    check_s: float = 0.0  # wall time of the latest REPL check (kernel-cost proxy)

    def score(self) -> tuple:
        return (self.accepted, -self.error_count, -self.sorry_count, -len(self.source))


# SUBMISSION_CLUSTER_REPAIR (research branch B3): pure clustering/transfer
# helpers — no I/O, unit-tested offline.


def cluster_near_misses(candidates: list[Candidate]) -> list[list[Candidate]]:
    """Group near-misses by `error_signature` fingerprint of their messages.

    Near-misses sharing a fingerprint are the same underlying mistake.
    Clusters come back largest first (stable on ties); within a cluster
    candidates are sorted by ascending error count (stable), so cluster[0]
    is the repair representative and cluster[1:] are the siblings a
    successful fix may be transferred to.
    """

    groups: dict[str, list[Candidate]] = {}
    for candidate in candidates:
        groups.setdefault(error_signature(candidate.messages), []).append(candidate)
    clusters = [sorted(group, key=lambda c: c.error_count)
                for group in groups.values()]
    clusters.sort(key=len, reverse=True)
    return clusters


def transfer_fix(failed_rep: str, repaired_rep: str, sibling: str) -> str | None:
    """Replay a representative's repair on a cluster sibling, textually.

    When the line diff failed_rep -> repaired_rep is a single contiguous
    replaced block and the removed block occurs verbatim (as whole lines)
    in `sibling`, return the sibling with its first occurrence substituted
    by the added block. Return None otherwise (multi-block or pure
    insert/delete diffs, or removed block absent from the sibling) — the
    fix is then not mechanically transferable. Pure text: callers must
    still guard and verify the result.
    """

    failed_lines = failed_rep.splitlines()
    repaired_lines = repaired_rep.splitlines()
    matcher = difflib.SequenceMatcher(a=failed_lines, b=repaired_lines, autojunk=False)
    edits = [op for op in matcher.get_opcodes() if op[0] != "equal"]
    if len(edits) != 1 or edits[0][0] != "replace":
        return None
    _tag, i1, i2, j1, j2 = edits[0]
    removed = failed_lines[i1:i2]
    added = repaired_lines[j1:j2]
    sibling_lines = sibling.splitlines()
    for at in range(len(sibling_lines) - len(removed) + 1):
        if sibling_lines[at: at + len(removed)] == removed:
            patched = sibling_lines[:at] + added + sibling_lines[at + len(removed):]
            return "\n".join(patched) + ("\n" if sibling.endswith("\n") else "")
    return None


class Deadline:
    def __init__(self, config: Config):
        self.started = time.monotonic()
        self.soft = self.started + config.agent_time_s - config.margin_s

    def remaining(self) -> float:
        return self.soft - time.monotonic()

    def allows(self, seconds: float) -> bool:
        return self.remaining() > seconds


class LLMDead(Exception):
    """LLM budget/transport is gone; deterministic work may continue."""


def skeleton_portfolio_key(source: str) -> tuple[str, ...]:
    """Distinctness key of a decomposition: sorted distinct hole decl names.

    Two skeletons with the same key leave holes in the same declarations, so
    they count as the SAME decomposition for SUBMISSION_SKELETON_PORTFOLIO
    (the fewer-holes version supersedes — e.g. a partial fill that closed one
    of several sorries inside a helper); different keys are different plans.
    """

    return tuple(sorted({hole.decl_name for hole in parse_challenge(source).holes}))


class Toolbox:
    """Shared plumbing for all stages: checking, sampling, best-candidate."""

    def __init__(self, problem: Problem, services: Services, config: Config):
        self.problem = problem
        self.services = services
        self.config = config
        self.deadline = Deadline(config)
        # `challenge` is the working statement text: identical to the pristine
        # challenge except that S0.5 may pin numeric answer literals into it.
        self.challenge = problem.challenge
        self.parsed = parse_challenge(problem.challenge)
        self.best = Candidate(source=problem.challenge, origin="challenge",
                              sorry_count=len(self.parsed.holes))
        self.semaphore = asyncio.Semaphore(config.llm_concurrency)
        self.stage_log: list[dict[str, Any]] = []
        self.llm_alive = not config.disable_llm
        self.lemma_pool = ""  # proven helper lemmas, persistent across S4 cycles
        # gpt-oss rides a shared upstream pool that intermittently 429s, and one
        # HTTP error closes the whole problem ledger: keep gpt-oss to a single
        # in-flight call with a minimum gap between call starts (observed:
        # 1-in-5 calls hit a transient 429 burst during calibration).
        self.gptoss_gate = asyncio.Semaphore(1)
        self.gptoss_last_start = 0.0
        self.gptoss_gap_s = 5.0
        self.gptoss_calls = 0
        self.cycle = 0
        self.history_notes: list[str] = []  # compact per-cycle failure digest
        # SUBMISSION_CRITIC_NOTES (research branch B8): at most one gpt-oss
        # diagnosis call per problem; the slot burns even on a failed call.
        self.critic_notes_used = 0
        self.sorrify_seen: set = set()
        self.sorrify_used = 0
        self.last_unfilled: list[str] = []
        # Per-decl fill-failure counts (SUBMISSION_STRENGTHEN_IH): how many
        # times a hole in that decl ended its LLM rounds unfilled. Written
        # only when the flag is on; never persisted.
        self.fill_failures: dict[str, int] = {}
        # Verified Mathlib premise names for fill prompts (B5): None until
        # computed on the first fill pass; "" caches a failed/empty attempt.
        self._premise_hints: str | None = None
        # Best partial skeleton so far (SUBMISSION_SKELETON_KEEP): kept for
        # direct S4 resume instead of re-sketching from scratch, which throws
        # away filled holes that were not harvestable as standalone lemmas.
        # Ranking is (holes, errors) lexicographic; sentinels mean "none kept".
        self.kept_skeleton = ""
        self.kept_skeleton_holes = 10**6
        self.kept_skeleton_errors = 10**6
        # Two-slot portfolio (SUBMISSION_SKELETON_PORTFOLIO, independent of
        # SKELETON_KEEP): compiling partial skeletons of up to two DISTINCT
        # decompositions — keyed by skeleton_portfolio_key — so S4 fill effort
        # hedges across plans instead of funnelling into a possibly-wrong
        # round-1 skeleton. Entries: {"source": str, "holes": int, "key": tuple}.
        self.portfolio: list[dict[str, Any]] = []
        # A flaky REPL (container death, cold-boot import timeout) must degrade
        # the search, not crash the problem: after two consecutive failures we
        # stop checking and submit the best unverified candidate instead.
        self.lean_alive = True
        self.repl_failures = 0
        self.models_arm: list[str] = {
            "qwen": [QWEN], "gptoss": [GPTOSS]}.get(config.models, [QWEN, GPTOSS])
        # Durable progress (survives worker restarts under `run.py --resume`):
        # a resumed segment skips finished S0/S0.5 work, keeps proven lemmas
        # and failure history, and continues the cycle count. One-segment
        # judge runs simply write it and never read it back.
        self.s0_done = False
        self.cycles_done = 0
        self.pinned_answers: dict[str, int] = {}
        state_dir = getattr(services, "state_dir", None)
        self.state_path = Path(state_dir) / "agent_state.json" if state_dir else None
        self._load_state()

    def log(self, **kv: Any) -> None:
        self.stage_log.append(kv)

    def pin_answers(self, answers: dict[str, int]) -> None:
        """Replace `abbrev name : ℕ := sorry` bodies with agreed literals."""

        import re as _re
        text = self.challenge
        for name, value in answers.items():
            text = _re.sub(
                rf"(\babbrev\s+{_re.escape(name)}\s*:\s*(?:ℕ|Nat)\s*:=)\s*sorry",
                rf"\g<1> {value}", text)
        self.challenge = text
        self.parsed = parse_challenge(text)
        self.pinned_answers = dict(answers)

    def _state_key(self) -> str:
        return hashlib.sha256(self.problem.challenge.encode()).hexdigest()[:16]

    def _load_state(self) -> None:
        if self.state_path is None or not self.state_path.exists():
            return
        try:
            state = json.loads(self.state_path.read_text())
        except (OSError, ValueError):
            return
        if state.get("challenge_sha") != self._state_key():
            return
        self.s0_done = bool(state.get("s0_done"))
        self.cycles_done = max(0, int(state.get("cycles_done", 0)))
        self.lemma_pool = str(state.get("lemma_pool", ""))
        self.history_notes = [str(x) for x in state.get("history_notes", [])][-12:]
        if self.config.skeleton_keep:
            skeleton = state.get("kept_skeleton")
            if isinstance(skeleton, str) and 0 < len(skeleton) <= 40000:
                self.kept_skeleton = skeleton
                self.kept_skeleton_holes = max(0, int(state.get("kept_skeleton_holes", 10**6)))
                self.kept_skeleton_errors = max(0, int(state.get("kept_skeleton_errors", 10**6)))
        if self.config.skeleton_portfolio:
            stored = state.get("skeleton_portfolio")
            for entry in (stored if isinstance(stored, list) else [])[:2]:
                source = entry.get("source") if isinstance(entry, dict) else None
                key = entry.get("key") if isinstance(entry, dict) else None
                if isinstance(source, str) and 0 < len(source) <= 40000 \
                        and isinstance(key, list):
                    self.portfolio.append({
                        "source": source,
                        "holes": max(0, int(entry.get("holes", 0))),
                        "key": tuple(str(k) for k in key)})
        pinned = state.get("pinned_answers")
        if isinstance(pinned, dict):
            try:
                answers = {str(k): int(v) for k, v in pinned.items()}
            except (TypeError, ValueError):
                answers = {}
            if answers:
                self.pin_answers(answers)
        self.log(stage="resume", s0_done=self.s0_done, cycles_done=self.cycles_done,
                 pinned=list(self.pinned_answers), lemma_pool_bytes=len(self.lemma_pool))

    def save_state(self) -> None:
        if self.state_path is None:
            return
        state: dict[str, Any] = {
            "challenge_sha": self._state_key(),
            "s0_done": self.s0_done,
            "cycles_done": self.cycles_done,
            "lemma_pool": self.lemma_pool[-20000:],
            "history_notes": self.history_notes[-12:],
            "pinned_answers": self.pinned_answers,
        }
        # A truncated skeleton is not valid Lean, so an oversized one is
        # dropped from the state file rather than sliced to the cap.
        if self.config.skeleton_keep and 0 < len(self.kept_skeleton) <= 40000:
            state["kept_skeleton"] = self.kept_skeleton
            state["kept_skeleton_holes"] = self.kept_skeleton_holes
            state["kept_skeleton_errors"] = self.kept_skeleton_errors
        # Same rule for portfolio entries: oversized sources are dropped whole.
        if self.config.skeleton_portfolio:
            entries = [
                {"source": e["source"], "holes": e["holes"], "key": list(e["key"])}
                for e in self.portfolio if 0 < len(e["source"]) <= 40000]
            if entries:
                state["skeleton_portfolio"] = entries
        try:
            self.state_path.write_text(json.dumps(state))
        except OSError:
            pass

    def update_portfolio(self, source: str, holes: int) -> None:
        """Insert/replace one compiling partial skeleton in the two slots.

        Same key = same decomposition: the fewer-holes version wins. A new key
        adds a slot; beyond two distinct decompositions the most-holed entry
        is dropped.
        """

        key = skeleton_portfolio_key(source)
        for entry in self.portfolio:
            if entry["key"] == key:
                if holes < entry["holes"]:
                    entry["source"], entry["holes"] = source, holes
                return
        self.portfolio.append({"source": source, "holes": holes, "key": key})
        if len(self.portfolio) > 2:
            self.portfolio.remove(max(self.portfolio, key=lambda e: e["holes"]))

    def record(self, candidate: Candidate, stage: str) -> None:
        if candidate.score() > self.best.score():
            self.best = candidate
            self.services.checkpoint(candidate.source, {
                "stage": stage, "origin": candidate.origin,
                "accepted": candidate.accepted, "errors": candidate.error_count,
                "sorries": candidate.sorry_count,
            })

    async def check(self, candidate: Candidate, timeout_s: int = 90) -> Candidate:
        if not self.lean_alive:
            candidate.error_count = 10**6
            candidate.messages = [{"severity": "error", "data": "REPL unavailable"}]
            return candidate
        check_started = time.monotonic()
        try:
            result = await self.services.lean.check_file(candidate.source, timeout_s=timeout_s)
        except LeanRuntimeError as exc:
            self.repl_failures += 1
            self.log(stage="lean", error=str(exc)[:120], consecutive=self.repl_failures)
            if self.repl_failures >= 2:
                self.lean_alive = False
            candidate.error_count = 10**6
            candidate.messages = [{"severity": "error", "data": f"REPL unavailable: {exc}"}]
            return candidate
        self.repl_failures = 0
        candidate.check_s = time.monotonic() - check_started
        candidate.messages = result.messages
        candidate.error_count = sum(
            1 for m in result.messages if m.get("severity") == "error"
        ) + (10**6 if result.timed_out else 0)
        candidate.sorry_count = (
            len(parse_challenge(candidate.source).holes) if result.has_sorry else 0)
        candidate.accepted = result.accepted
        return candidate

    async def sample(self, model: str, messages: list[dict[str, str]], *,
                     kind: str, temperature: float | None = None,
                     max_tokens: int | None = None) -> str | None:
        """One guarded LLM call. kind: qwen-fast | qwen-think | gptoss-med | gptoss-high.

        `temperature`, when set, overrides the kind profile's value
        (SUBMISSION_WAVE_SPREAD); None keeps the profile unchanged.
        """

        if not self.llm_alive:
            raise LLMDead
        scaled = self.config.scaled
        params: dict[str, Any] = {
            "qwen-fast": dict(max_tokens=16000, temperature=0.8, reasoning=None,
                              timeout_s=int(scaled(self.config.qwen_call_s))),
            "qwen-think": dict(max_tokens=24000, temperature=0.7,
                               reasoning={"enabled": True, "max_tokens": 12000},
                               timeout_s=int(scaled(self.config.qwen_call_s + 300))),
            "qwen-deep": dict(max_tokens=28000, temperature=0.7,
                              reasoning={"enabled": True, "max_tokens": 16000},
                              timeout_s=int(scaled(self.config.qwen_call_s + 420))),
            "gptoss-med": dict(max_tokens=24000, temperature=1.0,
                               reasoning={"effort": "medium"},
                               timeout_s=int(scaled(self.config.gptoss_call_s))),
            "gptoss-high": dict(max_tokens=28000, temperature=1.0,
                                reasoning={"effort": "high"},
                                timeout_s=int(scaled(self.config.gptoss_call_s + 300))),
        }[kind]
        # SUBMISSION_WAVE_SPREAD (research branch B1): per-call override.
        if temperature is not None:
            params["temperature"] = temperature
        if max_tokens is not None:  # cheap auxiliary calls (B5 premise hints)
            params["max_tokens"] = max_tokens
        gate = self.gptoss_gate if model == GPTOSS else self.semaphore
        async with gate:
            if model == GPTOSS:
                # Every gpt-oss call is a mortality dice-roll for the whole
                # problem ledger (observed: 429s, 502s, truncated bodies), so a
                # hard per-problem cap bounds the cumulative risk.
                if self.gptoss_calls >= self.config.gptoss_call_cap:
                    return None
                self.gptoss_calls += 1
                gap = self.gptoss_gap_s - (time.monotonic() - self.gptoss_last_start)
                if gap > 0:
                    await asyncio.sleep(gap)
                self.gptoss_last_start = time.monotonic()
            if not self.deadline.allows(params["timeout_s"] + 60):
                return None
            try:
                response = await self.services.llm.complete(
                    model=model, messages=messages, **params)
            except LLMCallError as exc:
                # Under the shipped kit any HTTP failure has already closed the
                # ledger, so the next reservation raises BudgetAccountingError
                # below and we die then. Under the kit fix in flight upstream
                # (zero-cost refusals release instead of closing), the ledger
                # survives — treating this as one wasted sample lets the run
                # recover automatically once that lands.
                self.log(stage="llm", call_error=type(exc).__name__,
                         detail=str(exc)[:120])
                return None
            except (BudgetAccountingError, BudgetExceeded, LLMPolicyError) as exc:
                self.llm_alive = False
                self.log(stage="llm", died=type(exc).__name__)
                raise LLMDead from exc
        if response.finish_reason == "error" or not response.content:
            return None  # provider hiccup (content filter etc.) — sample wasted
        return response.content

    async def premise_hints(self) -> str:
        """Verified-premise block for S4 fill prompts (SUBMISSION_PREMISE_HINTS).

        One cheap qwen-fast call proposes likely-relevant Mathlib lemma
        names; one batched `#check` file keeps only the names this Mathlib
        actually has (a `#check` line errors iff its name is unknown), so
        fill prompts only ever see verified names. Computed lazily once per
        problem; any failure caches "" so the fill loop never pays twice.
        """

        if self._premise_hints is not None:
            return self._premise_hints
        hints = ""
        try:
            # QWEN-arm-gated (arm isolation, like every stage): the qwen-fast
            # proposer must not leak into a gptoss-only research arm.
            if QWEN in self.models_arm and self.llm_alive and self.lean_alive \
                    and self.deadline.allows(240):
                text = await self.sample(
                    QWEN, premise_messages(self.problem, self.challenge),
                    kind="qwen-fast", max_tokens=1000)
                names = parse_premise_names(text or "")
                if names:
                    # Imports first, then exactly one `#check` per line: the
                    # REPL strips import lines (the _sorrify_progress
                    # accounting), so kept line k maps to candidate k-1.
                    source = "\n".join(
                        self.parsed.imports
                        + [f"#check {name}" for name in names]) + "\n"
                    probe = Candidate(source=source, origin="premise-hints")
                    await self.check(probe, timeout_s=60)
                    if probe.error_count < 10**6:  # REPL alive, no timeout
                        failed = failed_premise_indexes(probe.messages, len(names))
                        kept = [name for index, name in enumerate(names)
                                if index not in failed]
                        if kept:
                            hints = ("Verified available lemmas (these names "
                                     "exist; prefer them):\n"
                                     + "\n".join(f"- {name}" for name in kept))
                        self.log(stage="S4-premises", proposed=len(names),
                                 verified=len(kept))
        except Exception as exc:  # hints must never break the fill loop
            self.log(stage="S4-premises", error=type(exc).__name__)
            hints = ""
        self._premise_hints = hints
        return hints


# ---------------------------------------------------------------------------
# The agent


class SubmissionAgent:
    def __init__(self, config: Config | None = None):
        self.config = config or Config.from_env()

    async def solve(self, problem: Problem, services: Services) -> AgentResult:
        toolbox = Toolbox(problem, services, self.config)
        solved: Candidate | None = None
        heavy_fallback: Candidate | None = None

        def guard_heavy(candidate: Candidate | None) -> Candidate | None:
            # The comparator rebuilds the file cold under a 180 s cap that
            # also covers the challenge build and two kernel exports, leaving
            # ~60-90 s for the solution — and cold elaboration is slower than
            # the warm REPL (observed twice on p10: REPL-accepted proofs, 40 s
            # guard silent, comparator timeout at 180.9 s). While ample time
            # remains, hold a >15 s win as fallback and hunt a lighter one.
            nonlocal heavy_fallback
            if candidate is None or candidate.check_s <= 15 \
                    or not toolbox.deadline.allows(toolbox.config.scaled(1800)):
                return candidate
            if heavy_fallback is None or candidate.check_s < heavy_fallback.check_s:
                heavy_fallback = candidate
            toolbox.log(stage="S5-guard", deferred=candidate.origin,
                        check_s=round(candidate.check_s, 1))
            return None

        try:
            if toolbox.parsed.numeric_answer_names and toolbox.llm_alive \
                    and not toolbox.pinned_answers:
                await self.stage05_answers(toolbox)
                if toolbox.pinned_answers:
                    toolbox.save_state()
            if not toolbox.s0_done:
                solved = guard_heavy(await self.stage0_sweep(toolbox))
                if solved is None and toolbox.lean_alive:
                    toolbox.s0_done = True
                    toolbox.save_state()
            # Anytime loop: alternate fresh diverse sampling (coverage) with
            # decomposition (depth) until solved, the LLM dies, or time runs low.
            # Eight cycles fill a 30–120 min window, but would strand hours at
            # the judge's 8-hour cap; scale the cap with the window instead.
            max_cycles = max(8, int(self.config.agent_time_s // 1500))
            cycle = toolbox.cycles_done
            prechecks = 0
            while True:
                # The cycle cap is calibrated for ~25-min mixed-model cycles; when
                # one channel is refusing, all-qwen cycles run far faster and the
                # cap would strand hours of window — so past the cap, keep cycling
                # while ≥45 min of window remains (short windows are unaffected:
                # they exhaust the deadline check before the cap matters).
                while solved is None and toolbox.llm_alive and toolbox.lean_alive \
                        and (cycle < max_cycles or toolbox.deadline.allows(2700.0)) \
                        and toolbox.deadline.allows(toolbox.config.scaled(600)):
                    cycle += 1
                    toolbox.cycle = cycle
                    # Sampling banks coverage; decomposition gets the next slice
                    # of the window (it is the hard-tier weapon and needs room);
                    # whole-file repair mops up with whatever time remains.
                    solved, near_misses = await self.stage1_sample(toolbox)
                    if solved is None and toolbox.lean_alive \
                            and toolbox.deadline.allows(toolbox.config.scaled(900)):
                        solved = await self.stage4_decompose(toolbox)
                    if solved is None and toolbox.lean_alive:
                        solved = await self.stage2_repair(toolbox, near_misses)
                    solved = guard_heavy(solved)
                    toolbox.cycles_done = cycle
                    toolbox.save_state()
                # The warm REPL cannot observe cold-build kernel cost (three
                # p10 proofs were REPL-accepted, then timed out the
                # comparator's 180 s build). When the real gate is available
                # and time permits, verify the winner against it; a timeout
                # demotes the proof to fallback and resumes the hunt.
                compare = getattr(toolbox.services, "compare", None)
                if solved is None or not solved.accepted or compare is None \
                        or not self.config.compare_precheck or prechecks >= 2 \
                        or not toolbox.deadline.allows(360):
                    break
                prechecks += 1
                try:
                    verdict = await asyncio.to_thread(compare, solved.source)
                except Exception as exc:
                    toolbox.log(stage="S5-precheck", error=str(exc)[:120])
                    break
                toolbox.log(stage="S5-precheck", origin=solved.origin,
                            passed=bool(verdict.get("passed")),
                            timed_out=bool(verdict.get("timed_out")),
                            duration_ms=verdict.get("duration_ms"))
                if verdict.get("passed") or not verdict.get("timed_out"):
                    # Confirmed — or rejected for a reason further REPL-guided
                    # search cannot fix better than S5's audit; ship it.
                    break
                if heavy_fallback is None or solved.check_s < heavy_fallback.check_s:
                    heavy_fallback = solved
                solved = None
        except LLMDead:
            pass  # deterministic results stand; finalize below

        final = solved or heavy_fallback or toolbox.best
        if final.accepted and toolbox.lean_alive and toolbox.deadline.allows(120):
            # Re-verify and audit axioms in one pass: `#print axioms` reports the
            # dependency set the Comparator will enforce (catches native_decide).
            audit_source = final.source.rstrip() + "\n\n" + "\n".join(
                f"#print axioms {name}" for name in toolbox.parsed.decl_names) + "\n"
            audit = Candidate(source=audit_source, origin=final.origin)
            await toolbox.check(audit, timeout_s=90)
            violations = axiom_violations(audit.messages)
            if audit.error_count > 0 or violations:
                final.accepted = False
                toolbox.log(stage="S5", reverify_errors=audit.error_count,
                            axiom_violations=violations)
        services.checkpoint(final.source, {
            "stage": "final", "origin": final.origin, "accepted": final.accepted,
        })
        return AgentResult(final.source, {
            "agent": "coordination-v2",
            "arm": self.config.models,
            "origin": final.origin,
            "accepted_by_repl": final.accepted,
            "stages": toolbox.stage_log,
            "wall_s": round(time.monotonic() - toolbox.deadline.started, 1),
        })

    # ---- S0.5: cross-model answer consensus --------------------------------

    async def stage05_answers(self, tb: Toolbox) -> None:
        """Pin numeric answer literals agreed on by both models.

        A wrong answer poisons the whole proof search, and the verifier cannot
        reject it quickly — this is the one decision where cross-model
        consensus genuinely pays (RESEARCH.md §6.1).
        """

        names = tb.parsed.numeric_answer_names
        if tb.config.models == "duo":
            askers = [(QWEN, "qwen-think"), (GPTOSS, "gptoss-high")]
            judge = (GPTOSS, "gptoss-high")
        elif tb.config.models == "qwen":
            askers = [(QWEN, "qwen-think"), (QWEN, "qwen-think")]
            judge = (QWEN, "qwen-think")
        else:
            askers = [(GPTOSS, "gptoss-high"), (GPTOSS, "gptoss-high")]
            judge = (GPTOSS, "gptoss-high")

        # Sequential, qwen first: a gpt-oss 429 closes the ledger, so bank the
        # cheaper derivation before touching the risky channel.
        texts: list[Any] = []
        for model, kind in askers:
            texts.append(await tb.sample(
                model, answer_messages(tb.problem, tb.challenge, names), kind=kind))
        parsed = [parse_answer_lines(t, names) if isinstance(t, str) else None
                  for t in texts]
        a1, a2 = (parsed + [None, None])[:2]

        answers: dict[str, int] | None = None
        verdict = ""
        if a1 is not None and a1 == a2:
            answers, verdict = a1, "agree"
        elif a1 is not None and a2 is not None:
            digest = "\n\n---\n\n".join(
                (t or "")[-2500:] for t in texts if isinstance(t, str))
            text = await tb.sample(
                judge[0], answer_messages(tb.problem, tb.challenge, names, digest),
                kind=judge[1])
            adjudicated = parse_answer_lines(text, names) if text else None
            answers = adjudicated or None
            if answers is not None and answers not in (a1, a2):
                # A third distinct answer is a red flag; prefer the majority-free
                # adjudication anyway but record the instability.
                verdict = "adjudicated-novel"
            else:
                verdict = "adjudicated"
        else:
            answers = a1 or a2
            verdict = "single" if answers else "none"
        if answers:
            tb.pin_answers(answers)
        tb.log(stage="S0.5", verdict=verdict,
               answers={k: str(v) for k, v in (answers or {}).items()},
               candidates=[{k: str(v) for k, v in (a or {}).items()} or None
                           for a in (a1, a2)])

    # ---- S0 ----------------------------------------------------------------

    async def stage0_sweep(self, tb: Toolbox) -> Candidate | None:
        if not tb.parsed.holes or tb.parsed.has_term_holes:
            tb.log(stage="S0", ran=False)
            return None
        for tactic, preamble in SWEEP:
            if not tb.deadline.allows(90) or not tb.lean_alive:
                break
            source = splice_tactics(tb.challenge, tactic, preamble)
            if source is None:
                break
            candidate = Candidate(source=source, origin=f"sweep:{tactic.splitlines()[0]}")
            await tb.check(candidate, timeout_s=60)
            tb.record(candidate, "S0")
            if candidate.accepted:
                tb.log(stage="S0", solved=candidate.origin)
                if tactic == "exact?":
                    concrete = await self._concretize_exact(tb, candidate)
                    if concrete is not None:
                        return concrete
                return candidate
        tb.log(stage="S0", solved=False)
        return None

    async def _concretize_exact(self, tb: Toolbox, accepted: Candidate) -> Candidate | None:
        for message in accepted.messages:
            data = str(message.get("data", ""))
            if TRY_THIS not in data:
                continue
            suggestion = data.split(TRY_THIS, 1)[1].strip()
            source = splice_tactics(tb.challenge, suggestion)
            if source is None:
                continue
            candidate = Candidate(source=source, origin=f"sweep:exact?→{suggestion[:40]}")
            await tb.check(candidate, timeout_s=60)
            tb.record(candidate, "S0")
            if candidate.accepted:
                return candidate
        return None

    # ---- S1 + S2/S3 --------------------------------------------------------

    async def _plan_first(self, tb: Toolbox) -> str:
        """SUBMISSION_PLAN_FIRST: majority-pick a short informal plan (DSP-lite).

        Measured problem: on several dev problems the whole cycle-1 S1 wave
        chases one wrong strategy. Three cheap qwen-fast plan samples plus a
        majority pick align the wave with a majority-good strategy instead.
        Returns "" (wave unconditioned) when qwen is absent, the budget cannot
        afford ~3 short calls, or no usable plan comes back.
        """

        if QWEN not in tb.models_arm:
            return ""
        # The three short calls run concurrently under tb.semaphore, so the
        # wall cost is ~one qwen window; demand that plus the slack the S4
        # entry gate uses, else skip the step entirely.
        if not tb.deadline.allows(tb.config.scaled(tb.config.qwen_call_s + 600)):
            return ""
        messages = plan_messages(tb.problem, tb.challenge)
        texts = await asyncio.gather(
            *(tb.sample(QWEN, messages, kind="qwen-fast") for _ in range(3)),
            return_exceptions=True)
        for item in texts:
            if isinstance(item, LLMDead):
                raise item
        plans = [t for t in texts if isinstance(t, str)]
        plan = pick_plan(plans)
        # Bound what a runaway sampler could inject into every wave prompt.
        plan = "\n".join(plan.strip().splitlines()[:8])[:1200] if plan else ""
        tb.log(stage="S1", plan_samples=len(plans), plan_picked=bool(plan))
        return plan

    async def stage1_sample(self, tb: Toolbox) -> tuple[Candidate | None, list[Candidate]]:
        # SUBMISSION_PLAN_FIRST (off by default): cheap plan-selection step
        # before the first wave only; later cycles are unchanged.
        plan = ""
        if self.config.plan_first and tb.cycle <= 1:
            plan = await self._plan_first(tb)
        # Value-before-risk: run the qwen wave to completion (generate AND
        # check) before the first gpt-oss call, so a gpt-oss 429 that kills the
        # ledger cannot cost us qwen's candidates.
        solo = len(tb.models_arm) == 1
        waves: list[list[tuple[str, str]]] = []
        if QWEN in tb.models_arm:
            fast = self.config.qwen_samples + (self.config.gptoss_samples if solo else 0)
            # SUBMISSION_WAVE_SPREAD (research branch B1): short windows fit
            # few cycles, so buy 2 extra ~$0.001 qwen-fast draws of coverage.
            if self.config.wave_spread and self.config.agent_time_s < 2400:
                fast += 2
            waves.append([(QWEN, "qwen-fast")] * fast + [(QWEN, "qwen-think")])
        # On long-cap runs, gpt-oss joins from cycle 2: its channel carries the
        # transport-mortality risk, and qwen still has cycles of value to bank
        # first. Under SUBMISSION_SHORTCAP at short windows it skips the S1
        # wave entirely — its ~2–5 min serialized calls halve the cycle count
        # a 20-minute window affords qwen (measured: iter-1, RESEARCH_LOOP.md)
        # — while keeping its S0.5 / S4-sketch / fill-escalation roles.
        # Solo arms are unaffected.
        defer_gptoss = (not solo) and self.config.agent_time_s >= 2400 and tb.cycle <= 1
        skip_gptoss = (not solo) and self.config.shortcap \
            and self.config.agent_time_s < 2400
        if GPTOSS in tb.models_arm and not defer_gptoss and not skip_gptoss:
            count = self.config.gptoss_samples + (self.config.qwen_samples + 1 if solo else 0)
            waves.append([(GPTOSS, "gptoss-med")] * count)

        candidates: list[Candidate] = []
        seen: set[str] = set()
        for wave in waves:
            history = "\n".join(tb.history_notes[-6:]) if tb.cycle > 1 else ""
            # SUBMISSION_WAVE_SPREAD (research branch B1): the qwen-fast
            # samples (the wave prefix) cycle the temperature spread; None
            # entries keep each kind profile's own temperature.
            temps: list[float | None] = [
                wave_spread_temperature(i)
                if self.config.wave_spread and kind == "qwen-fast" else None
                for i, (_model, kind) in enumerate(wave)]
            texts = await asyncio.gather(
                *(tb.sample(model, whole_proof_messages(
                    tb.problem, tb.challenge, history=history,
                    plan=plan if kind == "qwen-fast" else ""), kind=kind,
                            temperature=temp)
                  for (model, kind), temp in zip(wave, temps)),
                return_exceptions=True)
            for item in texts:
                if isinstance(item, LLMDead):
                    raise item
            usable: list[Candidate] = []
            rejected = 0
            for (model, kind), text in zip(wave, texts):
                source = extract_lean(text) if isinstance(text, str) else None
                if not source:
                    continue
                guarded, _reason = guard_candidate(source, tb.parsed)
                if not guarded:
                    rejected += 1
                    continue
                if guarded in seen:
                    continue
                seen.add(guarded)
                usable.append(Candidate(source=guarded, origin=f"{kind}:s1"))
            tb.log(stage="S1", wave=wave[0][1], planned=len(wave),
                   usable=len(usable), rejected=rejected)
            if not tb.lean_alive and usable:
                # No verifier left: submit the best-effort candidate rather
                # than the raw challenge — a plausible whole proof can still
                # pass the Comparator even though we cannot pre-check it.
                unverified = usable[0]
                unverified.origin += ":unverified"
                tb.services.checkpoint(unverified.source, {
                    "stage": "S1", "origin": unverified.origin, "accepted": False})
                tb.best = unverified
                tb.log(stage="S1", unverified_submit=unverified.origin)
                return unverified, []
            for candidate in usable:
                if not tb.deadline.allows(120):
                    return None, candidates
                await tb.check(candidate)
                tb.record(candidate, "S1")
                if candidate.accepted:
                    tb.log(stage="S1", solved=candidate.origin)
                    return candidate, []
            if usable:
                closest = min(usable, key=lambda c: c.error_count)
                head = next((str(m.get("data", "")).splitlines()[0][:90]
                             for m in closest.messages
                             if m.get("severity") == "error"), "no errors surfaced")
                tb.history_notes.append(
                    f"cycle {tb.cycle}, {wave[0][1]} x{len(wave)}: best had "
                    f"{closest.error_count} errors; first: {head}")
            candidates.extend(usable)
        return None, candidates

    async def stage2_repair(self, tb: Toolbox,
                            candidates: list[Candidate]) -> Candidate | None:
        candidates = sorted(candidates, key=lambda c: c.error_count)
        targets = candidates[:2]
        clusters: list[list[Candidate]] = []
        if self.config.cluster_repair:
            # SUBMISSION_CLUSTER_REPAIR (research branch B3): near-misses that
            # share an error fingerprint are the same underlying mistake — put
            # the unchanged repair budget on one representative per cluster
            # (fewest errors in it), largest cluster first, instead of burning
            # repair dialogues on duplicates.
            clusters = cluster_near_misses(candidates)
            targets = [cluster[0] for cluster in clusters[:2]]
        for index, candidate in enumerate(targets):
            result = await self.repair_with_handoff(
                tb, candidate,
                origin_model=QWEN if candidate.origin.startswith("qwen") else GPTOSS,
                build_messages=lambda fb: whole_proof_messages(tb.problem, tb.challenge, feedback=fb),
                guard=lambda src: guard_candidate(src, tb.parsed)[0],
                stage="S2")
            if result is not None:
                if clusters and result.accepted:
                    # B3: an accepted repair may transfer to the siblings that
                    # failed the same way — textual replay, no LLM calls.
                    await self._transfer_cluster_fix(
                        tb, candidate.source, result, clusters[index][1:])
                return result
        tb.log(stage="S2", solved=False)
        # SUBMISSION_CRITIC_NOTES (research branch B8): a repair pass that
        # closed nothing ends with one bounded gpt-oss diagnosis of the best
        # near-miss; the note reaches later S1 waves through history_notes
        # and gates nothing (RESEARCH.md §4.2: critique is a hint, no judge).
        if self.config.critic_notes and candidates:
            await self._critic_note(tb, candidates[0])
        return None

    async def _transfer_cluster_fix(self, tb: Toolbox, failed_rep: str,
                                    repaired: Candidate,
                                    siblings: list[Candidate]) -> None:
        """SUBMISSION_CLUSTER_REPAIR (B3): replay an accepted repair on up to
        three cluster siblings — a textual transplant plus one REPL check
        each, never an LLM call. Accepted transfers are recorded (and so
        checkpointed) as spare proofs; the caller still returns the
        representative's own repair."""

        for sibling in siblings[:3]:
            if not tb.deadline.allows(120):
                return
            patched = transfer_fix(failed_rep, repaired.source, sibling.source)
            if patched is None:
                continue
            guarded, _reason = guard_candidate(patched, tb.parsed)
            if guarded is None:
                continue
            transferred = Candidate(source=guarded,
                                    origin=sibling.origin + ":transfer")
            await tb.check(transferred)
            tb.record(transferred, "S2")
            tb.log(stage="S2", transfer=transferred.origin,
                   accepted=transferred.accepted, errors=transferred.error_count)

    async def _critic_note(self, tb: Toolbox, near_miss: Candidate) -> None:
        """One capped gpt-oss diagnosis per problem (SUBMISSION_CRITIC_NOTES).

        Skips unless the arm includes gpt-oss, the once-per-problem slot is
        unused, and the deadline affords a gpt-oss call (Toolbox.sample still
        enforces the gpt-oss call cap and start gap). The slot burns before
        the call: a None return skips silently and is never retried; LLMDead
        propagates like every other call site.
        """

        if tb.critic_notes_used or GPTOSS not in tb.models_arm:
            return
        call_s = tb.config.scaled(tb.config.gptoss_call_s)
        if not tb.deadline.allows(call_s + 180):
            return
        tb.critic_notes_used = 1
        text = await tb.sample(
            GPTOSS,
            critic_messages(tb.problem, near_miss.source,
                            format_messages(near_miss.messages)),
            kind="gptoss-med")
        if not text:
            tb.log(stage="S2", critic=False)
            return
        tb.history_notes.append("gpt-oss diagnosis: " + text.strip()[:800])
        tb.log(stage="S2", critic=True)

    # ---- S2/S3 core: capped repair with plateau handoff --------------------

    async def repair_with_handoff(
        self, tb: Toolbox, candidate: Candidate, *, origin_model: str,
        build_messages: Callable[[str], list[dict[str, str]]],
        guard: Callable[[str], str | None], stage: str,
        success: Callable[[Candidate], bool] | None = None,
    ) -> Candidate | None:
        """Deterministic fixes, then error-informed rounds; alternate model on plateau."""

        success = success or (lambda c: c.accepted)
        fixed = self._deterministic_fixes(candidate)
        if fixed is not None:
            await tb.check(fixed)
            tb.record(fixed, stage)
            if success(fixed):
                return fixed
            if fixed.score() > candidate.score():
                candidate = fixed

        model = origin_model if origin_model in tb.models_arm else tb.models_arm[0]
        last_signature = error_signature(candidate.messages)
        for round_index in range(self.config.repair_rounds):
            call_kind = ("qwen-think" if model == QWEN else "gptoss-med")
            call_s = tb.config.scaled(
                tb.config.qwen_call_s if model == QWEN else tb.config.gptoss_call_s)
            if not tb.deadline.allows(call_s + 180):
                return None
            text = await tb.sample(model, build_messages(format_messages(candidate.messages)),
                                   kind=call_kind)
            source = extract_lean(text) if text else None
            guarded = guard(source) if source else None
            if guarded is not None:
                repaired = Candidate(
                    source=guarded,
                    origin=f"{'qwen' if model == QWEN else 'gptoss'}:{stage.lower()}:r{round_index + 1}")
                await tb.check(repaired)
                tb.record(repaired, stage)
                if success(repaired):
                    tb.log(stage=stage, solved=repaired.origin)
                    return repaired
                signature = error_signature(repaired.messages)
                plateau = signature == last_signature
                last_signature = signature
                if repaired.score() > candidate.score():
                    candidate = repaired
            else:
                plateau = True  # unusable output: treat as no progress
            if plateau:
                model = tb.config.other(model)  # S3: fresh priors + error history
        return None

    def _deterministic_fixes(self, candidate: Candidate) -> Candidate | None:
        text = " ".join(str(m.get("data", "")) for m in candidate.messages)
        lines = []
        if "exceeds the threshold" in text and "exponentiation.threshold" not in candidate.source:
            lines.append("set_option exponentiation.threshold 10000")
        if "maximum recursion depth" in text and "maxRecDepth" not in candidate.source:
            lines.append("set_option maxRecDepth 8000")
        if ("maximum number of heartbeats" in text or "deterministic) timeout" in text) \
                and "maxHeartbeats" not in candidate.source:
            lines.append("set_option maxHeartbeats 1000000")
        if not lines:
            return None
        return Candidate(source=insert_preamble(candidate.source, "\n".join(lines)),
                         origin=candidate.origin + "+setopt")

    # ---- S4: sketch / fill -------------------------------------------------

    async def stage4_decompose(self, tb: Toolbox) -> Candidate | None:
        lemma_pool = tb.lemma_pool
        note = ""
        # Resume-first (SUBMISSION_SKELETON_KEEP): the best partial skeleton
        # re-enters the fill loop before any fresh sketch is paid for —
        # re-sketching from scratch throws away filled holes that were not
        # harvestable as standalone lemmas. Fresh sketching takes over once a
        # resume round stops closing holes; the skeleton stays kept for later
        # cycles unless a better partial displaces it.
        resume = tb.config.skeleton_keep and bool(tb.kept_skeleton)
        # Two-slot hedge (SUBMISSION_SKELETON_PORTFOLIO): even rounds resume
        # the best not-yet-resumed-this-cycle portfolio entry instead of
        # sketching, odd rounds sketch fresh — so both slots and fresh
        # decompositions all get fill turns across rounds.
        portfolio_resumed: set = set()
        for round_index in range(self.config.sketch_rounds):
            resumed, resume = resume, False
            slot: dict[str, Any] | None = None
            if tb.config.skeleton_portfolio and not resumed \
                    and round_index % 2 == 0:
                pending = [entry for entry in tb.portfolio
                           if entry["holes"] > 0
                           and entry["key"] not in portfolio_resumed]
                if pending:
                    slot = min(pending, key=lambda entry: entry["holes"])
                    portfolio_resumed.add(slot["key"])
            if resumed:
                entry_holes = tb.kept_skeleton_holes
                sketch = Candidate(source=tb.kept_skeleton,
                                   origin=f"sketch:kept:{round_index}")
                await tb.check(sketch)
            elif slot is not None:
                sketch = Candidate(source=slot["source"],
                                   origin=f"sketch:portfolio:{round_index}")
                await tb.check(sketch)
            else:
                # Time-adaptive sketcher: the deep reasoner when the window fits its
                # worst case, else the fast thinker — so decomposition still runs
                # under small wall-clock caps instead of never engaging.
                # qwen leads sketching: every observed ledger death has been a
                # gpt-oss transport kill, and the only hard-tier solve came off a
                # qwen-repaired skeleton. gpt-oss still alternates in when time is
                # roomy (its sketches carry real ideas — worth one dice-roll per
                # two rounds), but never carries the first round.
                available: list[tuple[str, str]] = []
                if QWEN in tb.models_arm \
                        and tb.deadline.allows(tb.config.scaled(tb.config.qwen_call_s + 600)):
                    available.append((QWEN, "qwen-think"))
                if GPTOSS in tb.models_arm and round_index > 0 \
                        and tb.deadline.allows(tb.config.scaled(tb.config.gptoss_call_s + 900)):
                    available.append((GPTOSS, "gptoss-high"))
                if not available:
                    break
                sketcher, kind = available[round_index % len(available)]
                text = await tb.sample(
                    sketcher, sketch_messages(tb.problem, tb.challenge, lemma_pool, note), kind=kind)
                source = extract_lean(text) if text else None
                guarded = guard_candidate(source, tb.parsed, allow_sorry=True)[0] if source else None
                if guarded is None:
                    note = "The previous sketch was rejected (statement altered or banned token)."
                    continue
                sketch = Candidate(source=guarded, origin=f"sketch:{kind}:{round_index}")
                await tb.check(sketch)
                if sketch.error_count > 0:
                    repaired = await self.repair_with_handoff(
                        tb, sketch, origin_model=sketcher,
                        build_messages=lambda fb: sketch_messages(
                            tb.problem, tb.challenge, lemma_pool,
                            f"Your sketch had compile errors, fix them (keep the sorries):\n{fb}"),
                        guard=lambda src: guard_candidate(src, tb.parsed, allow_sorry=True)[0],
                        stage="S4-skeleton",
                        success=lambda c: c.error_count == 0)
                    if repaired is None:
                        note = "The previous sketch did not compile; use simpler helper statements."
                        continue
                    sketch = repaired
            tb.record(sketch, "S4")
            tb.log(stage="S4", sketch=sketch.origin, holes=len(parse_challenge(sketch.source).holes))

            filled = await self._fill_holes(tb, sketch)
            if filled is not None and filled.accepted:
                tb.log(stage="S4", solved=filled.origin)
                return filled
            if tb.config.skeleton_keep and filled is not None:
                # Fewest-holes-first, fewer-errors tie-break; a hole-free
                # unaccepted file is never kept (nothing left to resume).
                holes_now = len(parse_challenge(filled.source).holes)
                if 0 < holes_now < tb.kept_skeleton_holes or (
                        holes_now == tb.kept_skeleton_holes
                        and filled.error_count < tb.kept_skeleton_errors):
                    tb.kept_skeleton = filled.source
                    tb.kept_skeleton_holes = holes_now
                    tb.kept_skeleton_errors = filled.error_count
                    tb.log(stage="S4", kept=filled.origin, kept_holes=holes_now)
                # A resume round holds the sketch slot only while it closes holes.
                resume = resumed and 0 < holes_now < entry_holes
            if tb.config.skeleton_portfolio and filled is not None:
                # Only a compiling, still-holed partial is portfolio material:
                # solved files returned above; broken ones cannot be resumed.
                portfolio_holes = len(parse_challenge(filled.source).holes)
                if 0 < portfolio_holes and filled.error_count == 0:
                    tb.update_portfolio(filled.source, portfolio_holes)
                    tb.log(stage="S4", portfolio=[
                        entry["holes"] for entry in tb.portfolio])
            # harvest proven helper lemmas (error-free file: sorry-free decls compiled)
            if filled is not None:
                lemma_pool = self._harvest_lemmas(tb, filled.source) or lemma_pool
                tb.lemma_pool = lemma_pool
                tb.save_state()  # keep harvested lemmas across worker restarts
                note = ("A previous decomposition proved some helpers (reuse them) but "
                        "stalled on these subgoals, which were evidently too hard as "
                        "stated — replace them with smaller or different lemmas: "
                        + ", ".join(tb.last_unfilled or ["(unknown)"]))
                # B7 (SUBMISSION_STRENGTHEN_IH): "" unless the flag is on.
                note += strengthen_ih_note(tb, filled.source)
            else:
                note = "The previous decomposition stalled; try a different lemma structure."
        tb.log(stage="S4", solved=False)
        return None

    async def _fill_holes(self, tb: Toolbox, sketch: Candidate) -> Candidate | None:
        current = sketch.source
        # B5 (SUBMISSION_PREMISE_HINTS): REPL-verified Mathlib names, computed
        # once per problem on the first fill pass, injected into every fill
        # dialogue. "" while the flag is off — prompts are byte-identical.
        hints = await tb.premise_hints() if tb.config.premise_hints else ""
        if tb.config.fill_breadth:
            # Breadth pass first (SUBMISSION_FILL_BREADTH): sweep EVERY hole
            # with the cheap tactic cascade before any LLM dialogue — an
            # early hole's expensive dialogue must not starve later holes a
            # one-line tactic closes (iter-2: m06 filled 0 of 8 holes).
            swept = True
            while swept:
                swept = False
                for index, hole in enumerate(parse_challenge(current).holes):
                    if not tb.deadline.allows(120):
                        break
                    if not hole.is_tactic:
                        continue
                    fill = await self._cascade_hole(tb, current, index, hole.decl_name)
                    if fill is not None:
                        current = fill
                        swept = True
                        partial = Candidate(source=current,
                                            origin=sketch.origin + ":partial")
                        await tb.check(partial)
                        tb.record(partial, "S4")
                        break  # re-parse: hole indices shifted
        progressed = True
        while progressed:
            holes = parse_challenge(current).holes
            if not holes:
                final = Candidate(source=current, origin=sketch.origin + ":filled")
                guarded = guard_candidate(current, tb.parsed)[0]
                if guarded is None:
                    return None
                final.source = guarded
                await tb.check(final)
                tb.record(final, "S4")
                return final
            progressed = False
            for index, hole in enumerate(holes):
                if not tb.deadline.allows(240):
                    break
                fill = await self._fill_one_hole(tb, current, index, hole.decl_name,
                                                 tactic_only=hole.is_tactic,
                                                 hints=hints)
                if fill is not None:
                    current = fill
                    progressed = True
                    partial = Candidate(source=current, origin=sketch.origin + ":partial")
                    await tb.check(partial)
                    tb.record(partial, "S4")
                    break  # re-parse: hole indices shifted
        remaining_holes = parse_challenge(current).holes
        tb.last_unfilled = sorted({h.decl_name for h in remaining_holes if h.decl_name})
        tb.log(stage="S4", unfilled=len(remaining_holes), sketch=sketch.origin,
               unfilled_decls=tb.last_unfilled)
        partial = Candidate(source=current, origin=sketch.origin + ":stalled")
        await tb.check(partial)
        tb.record(partial, "S4")
        return partial

    async def _fill_one_hole(self, tb: Toolbox, current: str, index: int,
                             decl_name: str, *, tactic_only: bool,
                             hints: str = "") -> str | None:
        """Return the file with hole `index` filled (or sorrify-progressed).

        Depth over breadth (Delta Prover / Prover Agent / MechMath evidence):
        one burst of up to three candidate scripts seeds a sequential repair
        dialogue on the best failure, alternating models on plateau; a failed
        script's scaffolding is preserved by truncating at the first error and
        recursing on the smaller hole (MechMath sorrifier) rather than being
        discarded.
        """

        from submission.lean_text import BANNED_RE, extract_all_blocks

        holes_before = len(parse_challenge(current).holes)
        if tactic_only and not tb.config.fill_breadth:  # breadth pass did this
            fill = await self._cascade_hole(tb, current, index, decl_name)
            if fill is not None:
                return fill

        technique = ""
        if tb.config.typed_fills and decl_name:
            # SUBMISSION_TYPED_FILLS (research branch B4): classify the hole's
            # enclosing declaration statement and append the matching
            # goal-class technique block to the fill dialogue.
            import re as _re
            statement = next(
                (s for s in parse_challenge(current).signatures
                 if _re.match(rf"\S+\s+{_re.escape(decl_name)}(?![A-Za-z0-9_'.])", s)),
                "")
            if statement:
                technique = FILL_TECHNIQUES.get(classify_goal(statement), "")

        suggest_note = ""
        if tb.config.suggest_harvest and tactic_only and tb.deadline.allows(180):
            # SUBMISSION_SUGGEST_HARVEST: the cascade's bare `exact?` closer
            # did not fire, but an `apply?` probe still emits "Try this:"
            # suggestions naming real Mathlib lemmas. Try the first few as
            # direct fills; failing that, hand them to the LLM rounds as hints.
            probe = Candidate(source=splice_holes(current, {index: "apply?"}),
                              origin=f"fill:{decl_name}:apply?")
            await tb.check(probe, timeout_s=60)
            suggestions = harvest_try_this(probe.messages)
            for suggestion in suggestions[:3]:
                if not tb.deadline.allows(90):
                    break
                spliced = splice_holes(current, {index: suggestion})
                attempt = Candidate(
                    source=spliced,
                    origin=f"fill:{decl_name}:harvest:{suggestion.splitlines()[0][:40]}")
                await tb.check(attempt, timeout_s=60)
                if attempt.error_count == 0 \
                        and len(parse_challenge(spliced).holes) < holes_before:
                    return spliced
            if suggestions:
                suggest_note = ("Lean's search suggests these may apply:\n- "
                                + "\n- ".join(s[:120] for s in suggestions[:5]))

        model, kind = QWEN, "qwen-think"
        if tb.config.fill_reasoning:
            kind = "qwen-deep"  # fills die on the real math — buy deeper thinks
        if model not in tb.models_arm:
            model = tb.models_arm[0]
            kind = kind if model == QWEN else "gptoss-high"
        feedback = suggest_note
        best_block: str | None = None
        best_fail: Candidate | None = None
        last_signature = None
        # 1 burst + up to 3 sequential repairs; under the breadth variant the
        # dialogue budget scales with the window so more holes get a turn.
        rounds = 4
        if tb.config.fill_breadth:
            rounds = max(1, round(4 * min(1.0, tb.config.agent_time_s / 2400.0)))
        for round_index in range(rounds):
            try:
                text = await tb.sample(
                    model, fill_messages(tb.problem, current, decl_name, feedback,
                                         hints=hints, technique=technique),
                    kind=kind)
            except LLMDead:
                break
            improved = False
            for block in (extract_all_blocks(text)[:3] if text else []):
                if BANNED_RE.search(block) or "import " in block:
                    continue
                spliced = splice_holes(current, {index: block})
                attempt = Candidate(
                    source=spliced, origin=f"fill:{decl_name}:{kind}:r{round_index}")
                await tb.check(attempt)
                if attempt.error_count == 0 \
                        and len(parse_challenge(spliced).holes) < holes_before:
                    return spliced
                if best_fail is None or attempt.error_count < best_fail.error_count:
                    best_fail, best_block = attempt, block
                    improved = True
                if not tb.deadline.allows(240):
                    return None
            plateau = not improved
            if best_fail is not None:
                signature = error_signature(best_fail.messages)
                plateau = plateau or signature == last_signature
                last_signature = signature
                feedback = ("Your best failed attempt so far:\n```lean\n"
                            + (best_block or "") + "\n```\n\nLean feedback:\n"
                            + format_messages(best_fail.messages, limit=3000))
                if suggest_note:
                    feedback += "\n\n" + suggest_note
            if plateau:
                model = tb.config.other(model)
                if model == GPTOSS:
                    kind = "gptoss-high"
                else:
                    kind = "qwen-deep" if tb.config.fill_reasoning else "qwen-think"

        # B7 bookkeeping (SUBMISSION_STRENGTHEN_IH): this hole's LLM rounds
        # ended without closing it — a mid-round deadline abort above says
        # nothing about the statement, so it deliberately skips the count.
        if tb.config.strengthen_ih and decl_name:
            tb.fill_failures[decl_name] = tb.fill_failures.get(decl_name, 0) + 1
        if best_block and best_fail:
            return await self._sorrify_progress(tb, current, index, best_block, best_fail)
        return None

    async def _cascade_hole(self, tb: Toolbox, current: str, index: int,
                            decl_name: str) -> str | None:
        """Try each FILL_SWEEP tactic on one hole; return the filled file.

        With SUBMISSION_BOUND_TEMPLATES, statements led by a bounded ∀
        (`∀ n, n ≤ K → …`, `∀ n < K, …`, `∀ n ∈ Finset.range K, …`) first
        get intro + interval_cases exhaustion templates, which the generic
        one-tactic entries cannot express (they lack the intro/bound
        scaffolding); same accept rule and deadline guards.
        """

        holes_before = len(parse_challenge(current).holes)
        tactics = FILL_SWEEP
        if tb.config.bound_templates and decl_name:
            import re as _re
            statement = next(
                (s for s in parse_challenge(current).signatures
                 if _re.match(rf"\S+\s+{_re.escape(decl_name)}(?![A-Za-z0-9_'.])", s)),
                "")
            tactics = bounded_intro_templates(statement) + tactics
        for tactic in tactics:
            if not tb.deadline.allows(90):
                return None
            spliced = splice_holes(current, {index: tactic})
            attempt = Candidate(source=spliced,
                                origin=f"fill:{decl_name}:{tactic.splitlines()[0]}")
            await tb.check(attempt, timeout_s=60)
            if attempt.error_count == 0 \
                    and len(parse_challenge(spliced).holes) < holes_before:
                return spliced
        return None

    async def _sorrify_progress(self, tb: Toolbox, current: str, index: int,
                                block: str, fail: Candidate) -> str | None:
        """Keep a failed fill's scaffolding: truncate at the first error line,
        append sorry, adopt if the smaller-holed file compiles cleanly."""

        if tb.sorrify_used >= 4:
            return None
        holes = parse_challenge(current).holes
        if index >= len(holes):
            return None
        # REPL strips import lines, so message line numbers index the kept lines.
        prefix_lines = current[: holes[index].start].splitlines() or [""]
        kept_before = [l for l in prefix_lines if not l.startswith("import ")]
        start_line = max(0, len(kept_before) - 1)  # 0-based line of the block start
        block_lines = block.splitlines()
        first_error_rel: int | None = None
        for message in fail.messages:
            if message.get("severity") != "error":
                continue
            line = (message.get("pos") or {}).get("line")
            if isinstance(line, int):
                rel = (line - 1) - start_line
                if 0 <= rel < len(block_lines):
                    first_error_rel = rel if first_error_rel is None \
                        else min(first_error_rel, rel)
        if not first_error_rel:  # None or 0: nothing salvageable
            return None
        truncated = "\n".join(block_lines[:first_error_rel] + ["sorry"])
        key = (index, truncated)
        if key in tb.sorrify_seen:
            return None
        spliced = splice_holes(current, {index: truncated})
        candidate = Candidate(source=spliced, origin="fill:sorrify")
        await tb.check(candidate)
        if candidate.error_count == 0:
            tb.sorrify_seen.add(key)
            tb.sorrify_used += 1
            tb.record(candidate, "S4")
            tb.log(stage="S4", sorrified=f"{first_error_rel} lines kept")
            return spliced
        return None

    def _harvest_lemmas(self, tb: Toolbox, source: str) -> str:
        """Extract sorry-free helper declarations from an error-free partial file."""

        from submission.lean_text import DECL_RE, SORRY_RE
        decls = list(DECL_RE.finditer(source))
        blocks: list[str] = []
        for i, decl in enumerate(decls):
            end = decls[i + 1].start() if i + 1 < len(decls) else len(source)
            segment = source[decl.start(): end].rstrip()
            if decl.group("name") in tb.parsed.decl_names:
                continue  # only helpers, never challenge declarations
            if SORRY_RE.search(segment):
                continue
            blocks.append(segment)
        return "\n\n".join(blocks)


def create_agent() -> SubmissionAgent:
    return SubmissionAgent()
