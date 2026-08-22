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
import os
import time
from dataclasses import dataclass, field
from typing import Any, Callable

from re_harness import AgentResult, Problem, Services
from re_harness.budget import BudgetAccountingError, BudgetExceeded
from re_harness.llm import LLMCallError, LLMPolicyError
from re_harness.models import MODEL_A as QWEN, MODEL_B as GPTOSS

from submission.lean_text import (
    Parsed,
    axiom_violations,
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

    # Worst-case single-call wall clock (observed: gpt-oss ~8 min on hard prompts).
    qwen_call_s: float = 300.0
    gptoss_call_s: float = 960.0
    llm_concurrency: int = 3

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
        )

    @property
    def agent_time_s(self) -> float:
        # Mirror worker.py: agent gets time_limit - min(reserve, 25% of limit).
        return max(1.0, self.time_limit_s - min(self.verify_reserve_s, self.time_limit_s * 0.25))

    @property
    def margin_s(self) -> float:
        return min(600.0, max(20.0, self.agent_time_s * 0.12))

    def other(self, model: str) -> str:
        if self.models == "qwen":
            return QWEN
        if self.models == "gptoss":
            return GPTOSS
        return GPTOSS if model == QWEN else QWEN


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
  positivity, field_simp; ring, gcongr, aesop, simp_all.
- This Mathlib deprecates `push_neg` (warning only); `by_contra h` then `push_neg at h`
  still works, or use `omega`-friendly reformulations."""

RULES_BLOCK = """Hard rules:
- Return ONE complete Lean file in a single ```lean code block.
- Keep every theorem/abbrev statement byte-for-byte identical to the challenge;
  you may add helper lemmas ABOVE the theorems.
- Never use admit, axiom, native_decide, or Lean 3 syntax.
- Numeric answer abbrevs (`abbrev … : ℕ :=`) must be plain decimal literals."""


def whole_proof_messages(problem: Problem, feedback: str = "",
                         history: str = "") -> list[dict[str, str]]:
    system = (
        "You are an expert Lean 4 / Mathlib prover. Produce a complete, compiling "
        "Lean file that proves the challenge theorem(s), replacing every `sorry`.\n"
        + RULES_BLOCK + "\n- Do not use sorry.\n\n" + COOKBOOK
    )
    user = [
        f"Problem {problem.id}:", problem.description, "",
        "Challenge file (fill in the sorries, change nothing else):",
        "```lean", problem.challenge.rstrip(), "```",
    ]
    if history:
        user += ["", "What has been tried so far (do something different):", history]
    if feedback:
        user += ["", "Lean compiler feedback on the previous attempt:",
                 "```", feedback, "```",
                 "Fix the reported problems. Return the full corrected file."]
    return [{"role": "system", "content": system},
            {"role": "user", "content": "\n".join(user)}]


def sketch_messages(problem: Problem, lemma_pool: str,
                    prior_note: str = "") -> list[dict[str, str]]:
    system = (
        "You are an expert Lean 4 / Mathlib prover planning a difficult proof by "
        "decomposition. Write a PROOF SKELETON: a complete Lean file where\n"
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
        "```lean", problem.challenge.rstrip(), "```",
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
                  feedback: str = "") -> list[dict[str, str]]:
    system = (
        "You are an expert Lean 4 / Mathlib prover. The file below compiles except "
        "for `sorry` placeholders. Replace ONLY the sorry inside the declaration "
        f"`{decl_name}` with a real proof. Keep everything else byte-for-byte "
        "identical (other sorries stay).\n"
        + RULES_BLOCK + "\n\n" + COOKBOOK
    )
    user = [
        f"Problem {problem.id} — current file:",
        "```lean", sketch.rstrip(), "```",
        "",
        f"Prove the `sorry` in `{decl_name}`. Return the complete updated file.",
    ]
    if feedback:
        user += ["", "Lean feedback on the previous attempt at this hole:",
                 "```", feedback, "```"]
    return [{"role": "system", "content": system},
            {"role": "user", "content": "\n".join(user)}]


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
              "exact?"]

TRY_THIS = "Try this:"


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

    def score(self) -> tuple:
        return (self.accepted, -self.error_count, -self.sorry_count, -len(self.source))


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


class Toolbox:
    """Shared plumbing for all stages: checking, sampling, best-candidate."""

    def __init__(self, problem: Problem, services: Services, config: Config):
        self.problem = problem
        self.services = services
        self.config = config
        self.deadline = Deadline(config)
        self.parsed = parse_challenge(problem.challenge)
        self.best = Candidate(source=problem.challenge, origin="challenge",
                              sorry_count=len(self.parsed.holes))
        self.semaphore = asyncio.Semaphore(config.llm_concurrency)
        self.stage_log: list[dict[str, Any]] = []
        self.llm_alive = not config.disable_llm
        self.lemma_pool = ""  # proven helper lemmas, persistent across S4 cycles
        self.models_arm: list[str] = {
            "qwen": [QWEN], "gptoss": [GPTOSS]}.get(config.models, [QWEN, GPTOSS])

    def log(self, **kv: Any) -> None:
        self.stage_log.append(kv)

    def record(self, candidate: Candidate, stage: str) -> None:
        if candidate.score() > self.best.score():
            self.best = candidate
            self.services.checkpoint(candidate.source, {
                "stage": stage, "origin": candidate.origin,
                "accepted": candidate.accepted, "errors": candidate.error_count,
                "sorries": candidate.sorry_count,
            })

    async def check(self, candidate: Candidate, timeout_s: int = 90) -> Candidate:
        result = await self.services.lean.check_file(candidate.source, timeout_s=timeout_s)
        candidate.messages = result.messages
        candidate.error_count = sum(
            1 for m in result.messages if m.get("severity") == "error"
        ) + (10**6 if result.timed_out else 0)
        candidate.sorry_count = (
            len(parse_challenge(candidate.source).holes) if result.has_sorry else 0)
        candidate.accepted = result.accepted
        return candidate

    async def sample(self, model: str, messages: list[dict[str, str]], *,
                     kind: str) -> str | None:
        """One guarded LLM call. kind: qwen-fast | qwen-think | gptoss-med | gptoss-high."""

        if not self.llm_alive:
            raise LLMDead
        params: dict[str, Any] = {
            "qwen-fast": dict(max_tokens=16000, temperature=0.8, reasoning=None,
                              timeout_s=int(self.config.qwen_call_s)),
            "qwen-think": dict(max_tokens=24000, temperature=0.7,
                               reasoning={"enabled": True, "max_tokens": 12000},
                               timeout_s=int(self.config.qwen_call_s) + 300),
            "gptoss-med": dict(max_tokens=24000, temperature=1.0,
                               reasoning={"effort": "medium"},
                               timeout_s=int(self.config.gptoss_call_s)),
            "gptoss-high": dict(max_tokens=28000, temperature=1.0,
                                reasoning={"effort": "high"},
                                timeout_s=int(self.config.gptoss_call_s) + 300),
        }[kind]
        async with self.semaphore:
            if not self.deadline.allows(params["timeout_s"] + 60):
                return None
            try:
                response = await self.services.llm.complete(
                    model=model, messages=messages, **params)
            except (LLMCallError, BudgetAccountingError, BudgetExceeded, LLMPolicyError) as exc:
                self.llm_alive = False
                self.log(stage="llm", died=type(exc).__name__)
                raise LLMDead from exc
        if response.finish_reason == "error" or not response.content:
            return None  # provider hiccup (content filter etc.) — sample wasted
        return response.content


# ---------------------------------------------------------------------------
# The agent


class SubmissionAgent:
    def __init__(self, config: Config | None = None):
        self.config = config or Config.from_env()

    async def solve(self, problem: Problem, services: Services) -> AgentResult:
        toolbox = Toolbox(problem, services, self.config)
        solved: Candidate | None = None
        try:
            solved = await self.stage0_sweep(toolbox)
            # Anytime loop: alternate fresh diverse sampling (coverage) with
            # decomposition (depth) until solved, the LLM dies, or time runs low.
            cycle = 0
            while solved is None and toolbox.llm_alive and cycle < 8 \
                    and toolbox.deadline.allows(1200):
                cycle += 1
                solved = await self.stage1_and_2(toolbox)
                if solved is None and toolbox.deadline.allows(1800):
                    solved = await self.stage4_decompose(toolbox)
        except LLMDead:
            pass  # deterministic results stand; finalize below

        final = solved or toolbox.best
        if final.accepted and toolbox.deadline.allows(120):
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

    # ---- S0 ----------------------------------------------------------------

    async def stage0_sweep(self, tb: Toolbox) -> Candidate | None:
        if not tb.parsed.holes or tb.parsed.has_term_holes:
            tb.log(stage="S0", ran=False)
            return None
        for tactic, preamble in SWEEP:
            if not tb.deadline.allows(90):
                break
            source = splice_tactics(tb.problem.challenge, tactic, preamble)
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
            source = splice_tactics(tb.problem.challenge, suggestion)
            if source is None:
                continue
            candidate = Candidate(source=source, origin=f"sweep:exact?→{suggestion[:40]}")
            await tb.check(candidate, timeout_s=60)
            tb.record(candidate, "S0")
            if candidate.accepted:
                return candidate
        return None

    # ---- S1 + S2/S3 --------------------------------------------------------

    async def stage1_and_2(self, tb: Toolbox) -> Candidate | None:
        plans: list[tuple[str, str]] = []
        for model in tb.models_arm:
            if model == QWEN:
                plans += [(QWEN, "qwen-fast")] * self.config.qwen_samples
                plans += [(QWEN, "qwen-think")] * (1 if len(tb.models_arm) == 1 else 1)
            else:
                plans += [(GPTOSS, "gptoss-med")] * self.config.gptoss_samples
        if len(tb.models_arm) == 1 and plans:  # solo arms get matched sample counts
            extra = (self.config.qwen_samples + self.config.gptoss_samples
                     + 1 - len(plans))
            plans += [plans[0]] * max(0, extra)

        texts = await asyncio.gather(
            *(tb.sample(model, whole_proof_messages(tb.problem), kind=kind)
              for model, kind in plans),
            return_exceptions=True)
        for item in texts:
            if isinstance(item, LLMDead):
                raise item

        candidates: list[Candidate] = []
        seen: set[str] = set()
        rejected = 0
        for (model, kind), text in zip(plans, texts):
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
            candidates.append(Candidate(source=guarded, origin=f"{kind}:s1"))
        tb.log(stage="S1", planned=len(plans), usable=len(candidates), rejected=rejected)

        for candidate in candidates:
            if not tb.deadline.allows(120):
                return None
            await tb.check(candidate)
            tb.record(candidate, "S1")
            if candidate.accepted:
                tb.log(stage="S1", solved=candidate.origin)
                return candidate

        candidates.sort(key=lambda c: c.error_count)
        for candidate in candidates[:2]:
            result = await self.repair_with_handoff(
                tb, candidate,
                origin_model=QWEN if candidate.origin.startswith("qwen") else GPTOSS,
                build_messages=lambda fb: whole_proof_messages(tb.problem, feedback=fb),
                guard=lambda src: guard_candidate(src, tb.parsed)[0],
                stage="S2")
            if result is not None:
                return result
        tb.log(stage="S2", solved=False)
        return None

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
            call_s = tb.config.qwen_call_s if model == QWEN else tb.config.gptoss_call_s
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
        sketchers = [m for m in (GPTOSS, QWEN) if m in tb.models_arm] or tb.models_arm
        for round_index in range(self.config.sketch_rounds):
            if not tb.deadline.allows(tb.config.gptoss_call_s + 600):
                break
            sketcher = sketchers[round_index % len(sketchers)]
            kind = "gptoss-high" if sketcher == GPTOSS else "qwen-think"
            text = await tb.sample(
                sketcher, sketch_messages(tb.problem, lemma_pool, note), kind=kind)
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
                        tb.problem, lemma_pool,
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
            # harvest proven helper lemmas (error-free file: sorry-free decls compiled)
            if filled is not None:
                lemma_pool = self._harvest_lemmas(tb, filled.source) or lemma_pool
                tb.lemma_pool = lemma_pool
                note = "A previous decomposition proved some helpers (reuse them) but stalled."
            else:
                note = "The previous decomposition stalled; try a different lemma structure."
        tb.log(stage="S4", solved=False)
        return None

    async def _fill_holes(self, tb: Toolbox, sketch: Candidate) -> Candidate | None:
        current = sketch.source
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
                                                 tactic_only=hole.is_tactic)
                if fill is not None:
                    current = fill
                    progressed = True
                    partial = Candidate(source=current, origin=sketch.origin + ":partial")
                    await tb.check(partial)
                    tb.record(partial, "S4")
                    break  # re-parse: hole indices shifted
        remaining = len(parse_challenge(current).holes)
        tb.log(stage="S4", unfilled=remaining, sketch=sketch.origin)
        partial = Candidate(source=current, origin=sketch.origin + ":stalled")
        await tb.check(partial)
        tb.record(partial, "S4")
        return partial

    async def _fill_one_hole(self, tb: Toolbox, current: str, index: int,
                             decl_name: str, *, tactic_only: bool) -> str | None:
        """Return the file with hole `index` filled and no new errors, else None."""

        holes_before = len(parse_challenge(current).holes)
        if tactic_only:
            for tactic in FILL_SWEEP:
                if not tb.deadline.allows(90):
                    return None
                spliced = splice_holes(current, {index: tactic})
                attempt = Candidate(source=spliced,
                                    origin=f"fill:{decl_name}:{tactic.splitlines()[0]}")
                await tb.check(attempt, timeout_s=60)
                if attempt.error_count == 0 \
                        and len(parse_challenge(spliced).holes) < holes_before:
                    return spliced
        # LLM fills: cheap qwen first, escalate once to gpt-oss high. A dead LLM
        # leaves the hole unfilled but lets the cascade keep working other holes.
        attempts = [(QWEN, "qwen-think"), (QWEN, "qwen-think"), (GPTOSS, "gptoss-high")]
        feedback = ""
        for model, kind in attempts:
            if model not in tb.models_arm:
                continue
            try:
                text = await tb.sample(
                    model, fill_messages(tb.problem, current, decl_name, feedback), kind=kind)
            except LLMDead:
                return None
            source = extract_lean(text) if text else None
            guarded = guard_candidate(source, tb.parsed, allow_sorry=True)[0] if source else None
            if guarded is None:
                continue
            attempt = Candidate(source=guarded, origin=f"fill:{decl_name}:{kind}")
            await tb.check(attempt)
            before = len(parse_challenge(current).holes)
            after = len(parse_challenge(guarded).holes)
            if attempt.error_count == 0 and after < before:
                return guarded
            feedback = format_messages(attempt.messages)
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
