"""Two-model coordination agent (v1: rails + deterministic sweep + pooled sampling + repair).

Design rationale, evidence, and the staged-ladder plan live in RESEARCH.md.
This file implements stages S0 (deterministic tactic sweep), S1 (pooled diverse
sampling from both models), and S2 (short compiler-feedback repair), plus the
safety rails the harness mechanics demand:

- self-managed deadline (the worker's cancel mid-LLM-call would void the score),
- one-way LLM degradation (any transport error closes the budget ledger, so we
  fall back to LLM-free mode instead of retrying),
- statement safety (S0 candidates are spliced into the pristine challenge, so
  statements are unchanged by construction; LLM candidates are verified against
  the pristine signatures),
- lexical bans (sorry/admit/native_decide/axiom never reach the final file),
- numeric answers normalized to decimal literals,
- checkpoint on every improvement, finalize before the worker's clock runs out.

Environment knobs (all optional; defaults are the submission configuration):
  SUBMISSION_MODELS        duo | qwen | gptoss   (part-2 arms; default duo)
  SUBMISSION_DISABLE_LLM   1 to run S0 only
  SUBMISSION_QWEN_SAMPLES  int, S1 samples from qwen (default 8)
  SUBMISSION_GPTOSS_SAMPLES int, S1 samples from gpt-oss (default 2)
  SUBMISSION_REPAIR_ROUNDS int, S2 rounds per candidate (default 2)
"""

from __future__ import annotations

import ast
import asyncio
import os
import re
import time
from dataclasses import dataclass, field
from typing import Any

from re_harness import AgentResult, Problem, Services
from re_harness.budget import BudgetAccountingError, BudgetExceeded
from re_harness.llm import LLMCallError, LLMPolicyError
from re_harness.models import MODEL_A as QWEN, MODEL_B as GPTOSS

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
    models: str  # duo | qwen | gptoss
    disable_llm: bool
    qwen_samples: int
    gptoss_samples: int
    repair_rounds: int

    # Worst-case single-call wall clock; no call starts unless this fits
    # before the soft deadline (observed: gpt-oss up to ~8 min on hard prompts).
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
            repair_rounds=_env_int("SUBMISSION_REPAIR_ROUNDS", 2, 0, 8),
        )

    @property
    def agent_time_s(self) -> float:
        # Mirror worker.py: agent gets time_limit - min(reserve, 25% of limit).
        return max(1.0, self.time_limit_s - min(self.verify_reserve_s, self.time_limit_s * 0.25))

    @property
    def margin_s(self) -> float:
        # Safety margin before the worker's own cancel fires.
        return min(600.0, max(20.0, self.agent_time_s * 0.12))


# ---------------------------------------------------------------------------
# Challenge parsing and candidate construction

DECL_RE = re.compile(
    r"^(?P<indent>[ \t]*)(?P<kw>theorem|lemma|abbrev|def|instance)\s+(?P<name>[A-Za-z0-9_'.]+)",
    re.MULTILINE,
)
SORRY_RE = re.compile(r"(?<![A-Za-z0-9_'])sorry(?![A-Za-z0-9_'])")
BANNED_RE = re.compile(
    r"(?<![A-Za-z0-9_'])(sorry|admit|native_decide|sorryAx)(?![A-Za-z0-9_'])|^\s*axiom\s",
    re.MULTILINE,
)
FENCE_RE = re.compile(r"```(?:lean4?|Lean4?)?\s*\n(.*?)```", re.DOTALL)


@dataclass
class Hole:
    """One `sorry` in the pristine challenge."""

    start: int
    end: int
    indent: str
    is_tactic: bool  # preceded (modulo whitespace) by `by`; else a term hole


@dataclass
class Parsed:
    imports: list[str]
    holes: list[Hole]
    decl_names: list[str]
    signatures: list[str]  # normalized "kw name ... :=" text per sorry-decl
    numeric_answer_names: list[str]

    @property
    def has_term_holes(self) -> bool:
        return any(not hole.is_tactic for hole in self.holes)


def parse_challenge(challenge: str) -> Parsed:
    imports = [line for line in challenge.splitlines() if line.startswith("import ")]
    holes: list[Hole] = []
    for match in SORRY_RE.finditer(challenge):
        before = challenge[: match.start()]
        line_start = before.rfind("\n") + 1
        indent = re.match(r"[ \t]*", challenge[line_start:]).group(0)
        # `... := by\n  sorry` and `... := by sorry` -> tactic; `... := sorry` -> term.
        # A sorry in any other position (for example inside calc) counts as tactic,
        # the safest substitution target.
        stripped = before.rstrip()
        is_tactic = bool(re.search(r"\bby\b\s*$", stripped)) or not stripped.endswith(":=")
        holes.append(Hole(match.start(), match.end(), indent, is_tactic))
    decl_names = [m.group("name") for m in DECL_RE.finditer(challenge)]
    signatures = []
    numeric_answers = []
    decls = list(DECL_RE.finditer(challenge))
    for i, m in enumerate(decls):
        seg_end = decls[i + 1].start() if i + 1 < len(decls) else len(challenge)
        segment = challenge[m.start(): seg_end]
        assign_at = segment.find(":=")
        if assign_at >= 0:
            signatures.append(normalize_ws(segment[: assign_at + 2]))
        if m.group("kw") == "abbrev" and re.search(r":\s*(ℕ|Nat)\s*:=", segment):
            numeric_answers.append(m.group("name"))
    return Parsed(imports, holes, decl_names, signatures, numeric_answers)


def normalize_ws(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def splice_tactics(challenge: str, tactic: str, preamble: str = "") -> str | None:
    """Replace every tactic hole with `tactic`; None if any term hole exists.

    Statements are untouched by construction, which is what makes S0 safe.
    """

    parsed = parse_challenge(challenge)
    if not parsed.holes or parsed.has_term_holes:
        return None
    out: list[str] = []
    cursor = 0
    for hole in parsed.holes:
        out.append(challenge[cursor: hole.start])
        lines = tactic.splitlines() or [tactic]
        block = ("\n" + hole.indent).join(lines)
        out.append(block)
        cursor = hole.end
    out.append(challenge[cursor:])
    result = "".join(out)
    if preamble:
        result = insert_preamble(result, preamble)
    return result


def insert_preamble(source: str, preamble: str) -> str:
    """Insert set_option lines after the import block."""

    lines = source.splitlines()
    last_import = -1
    for i, line in enumerate(lines):
        if line.startswith("import "):
            last_import = i
    lines[last_import + 1: last_import + 1] = ["", preamble.rstrip()]
    return "\n".join(lines) + ("\n" if source.endswith("\n") else "")


def extract_lean(text: str) -> str | None:
    blocks = FENCE_RE.findall(text or "")
    if blocks:
        return blocks[-1].strip() + "\n"
    stripped = (text or "").strip()
    at = stripped.find("import ")
    if at >= 0:
        return stripped[at:] + "\n"
    return None


SAFE_BINOPS = (ast.Add, ast.Sub, ast.Mult, ast.FloorDiv, ast.Mod, ast.Pow)


def eval_nat_literal(expr: str) -> int | None:
    """Safely evaluate an arithmetic ℕ expression (e.g. `2^11 - 1`) to an int."""

    expr = expr.strip().rstrip(";").replace("^", "**")
    if not re.fullmatch(r"[0-9+\-*/%() \t*]{1,200}", expr):
        return None
    try:
        tree = ast.parse(expr, mode="eval")
    except SyntaxError:
        return None

    def walk(node: ast.AST) -> int:
        if isinstance(node, ast.Expression):
            return walk(node.body)
        if isinstance(node, ast.Constant) and isinstance(node.value, int):
            return node.value
        if isinstance(node, ast.BinOp) and isinstance(node.op, SAFE_BINOPS):
            left, right = walk(node.left), walk(node.right)
            if isinstance(node.op, ast.Pow) and (right > 10_000 or left > 10**6):
                raise ValueError("power too large")
            return {
                ast.Add: lambda: left + right,
                ast.Sub: lambda: left - right,
                ast.Mult: lambda: left * right,
                ast.FloorDiv: lambda: left // right,
                ast.Mod: lambda: left % right,
                ast.Pow: lambda: left ** right,
            }[type(node.op)]()
        raise ValueError("unsupported")

    try:
        value = walk(tree)
    except (ValueError, ZeroDivisionError, OverflowError, KeyError):
        return None
    return value if value >= 0 else None


def normalize_numeric_answers(source: str, names: list[str]) -> str:
    """Rewrite `abbrev name : ℕ := <expr>` bodies into decimal literals."""

    for name in names:
        pattern = re.compile(
            rf"(\babbrev\s+{re.escape(name)}\s*:\s*(?:ℕ|Nat)\s*:=)\s*([^\n]+)"
        )
        match = pattern.search(source)
        if not match:
            continue
        body = match.group(2).strip()
        if re.fullmatch(r"[0-9]+", body):
            continue
        value = eval_nat_literal(body)
        if value is not None:
            source = source[: match.start()] + f"{match.group(1)} {value}" + source[match.end():]
    return source


def guard_candidate(candidate: str, parsed: Parsed, pristine_imports: list[str]) -> tuple[str | None, str]:
    """Validate/normalize an LLM-written file. Returns (source, reason-if-rejected)."""

    if BANNED_RE.search(candidate):
        return None, "contains sorry/admit/native_decide/axiom"
    if "import " not in candidate:
        candidate = "\n".join(pristine_imports) + "\n\n" + candidate
    normalized = normalize_ws(candidate)
    for signature in parsed.signatures:
        if signature not in normalized:
            return None, f"statement altered or missing: {signature[:80]}"
    candidate = normalize_numeric_answers(candidate, parsed.numeric_answer_names)
    for name in parsed.numeric_answer_names:
        if not re.search(rf"\babbrev\s+{re.escape(name)}\s*:\s*(?:ℕ|Nat)\s*:=\s*[0-9]+\s*$",
                         candidate, re.MULTILINE):
            return None, f"numeric answer {name} is not a decimal literal"
    return candidate, ""


# ---------------------------------------------------------------------------
# Deterministic stage S0: tactic cocktail sweep (zero LLM cost)

OPTIONS_PREAMBLE = (
    "set_option maxHeartbeats 1000000\n"
    "set_option maxRecDepth 8000\n"
    "set_option exponentiation.threshold 10000"
)

# Ordered cheap-to-expensive; every entry is generic (rules: generic tactic
# libraries are explicitly allowed). Entries referencing hypothesis/variable
# names common in competition statements simply fail fast when absent.
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

TRY_THIS_RE = re.compile(r"Try this:\s*(.+)", re.DOTALL)


# ---------------------------------------------------------------------------
# Candidate bookkeeping


@dataclass
class Candidate:
    source: str
    origin: str  # e.g. "sweep:linarith", "qwen:s1:3", "gptoss:s2:r1"
    accepted: bool = False
    error_count: int = 10**6
    messages: list[dict[str, Any]] = field(default_factory=list)

    def score(self) -> tuple:
        return (self.accepted, -self.error_count, -len(self.source))


class Deadline:
    def __init__(self, config: Config):
        self.started = time.monotonic()
        self.soft = self.started + config.agent_time_s - config.margin_s

    def remaining(self) -> float:
        return self.soft - time.monotonic()

    def allows(self, seconds: float) -> bool:
        return self.remaining() > seconds


# ---------------------------------------------------------------------------
# The agent


class SubmissionAgent:
    def __init__(self, config: Config | None = None):
        self.config = config or Config.from_env()

    async def solve(self, problem: Problem, services: Services) -> AgentResult:
        config = self.config
        deadline = Deadline(config)
        parsed = parse_challenge(problem.challenge)
        best = Candidate(source=problem.challenge, origin="challenge")
        llm_alive = not config.disable_llm
        stage_log: list[dict[str, Any]] = []

        def better(candidate: Candidate) -> bool:
            return candidate.score() > best.score()

        def record(candidate: Candidate, stage: str) -> None:
            nonlocal best
            if better(candidate):
                best = candidate
                services.checkpoint(best.source, {
                    "stage": stage, "origin": best.origin,
                    "accepted": best.accepted, "errors": best.error_count,
                })

        async def check(candidate: Candidate, timeout_s: int) -> Candidate:
            result = await services.lean.check_file(candidate.source, timeout_s=timeout_s)
            candidate.accepted = result.accepted
            candidate.messages = result.messages
            candidate.error_count = sum(
                1 for m in result.messages if m.get("severity") == "error"
            ) + (10**6 if result.timed_out else 0)
            if result.has_sorry:
                candidate.accepted = False
                candidate.error_count += 10**6
            return candidate

        # ---- S0: deterministic sweep -------------------------------------
        solved = None
        if parsed.holes and not parsed.has_term_holes:
            for tactic, preamble in SWEEP:
                if not deadline.allows(90):
                    break
                source = splice_tactics(problem.challenge, tactic, preamble)
                if source is None:
                    break
                candidate = Candidate(source=source, origin=f"sweep:{tactic.splitlines()[0]}")
                await check(candidate, timeout_s=60)
                record(candidate, "S0")
                if candidate.accepted:
                    solved = candidate
                    # `exact?` found a proof: prefer the concrete suggestion so
                    # the comparator does not re-run the search.
                    if tactic == "exact?":
                        solved = await self._concretize_exact(
                            problem.challenge, candidate, check, record
                        ) or candidate
                    break
        stage_log.append({"stage": "S0", "solved": bool(solved),
                          "ran": parsed.holes != [] and not parsed.has_term_holes})

        # ---- S1/S2: LLM stages -------------------------------------------
        if solved is None and llm_alive:
            try:
                solved = await self._llm_stages(
                    problem, services, parsed, config, deadline, check, record, stage_log
                )
            except (LLMCallError, BudgetAccountingError):
                # Transport failure: the ledger is closed for good. Continue
                # without LLM rather than crashing the problem.
                llm_alive = False
                stage_log.append({"stage": "llm", "died": "transport"})
            except BudgetExceeded:
                llm_alive = False
                stage_log.append({"stage": "llm", "died": "budget"})
            except LLMPolicyError as exc:
                llm_alive = False
                stage_log.append({"stage": "llm", "died": f"policy: {exc}"})

        # ---- S5: finalize -------------------------------------------------
        final = solved or best
        if final.accepted and deadline.allows(90):
            confirm = Candidate(source=final.source, origin=final.origin)
            await check(confirm, timeout_s=60)
            if not confirm.accepted:
                final.accepted = False  # trust the fresh verdict
        services.checkpoint(final.source, {
            "stage": "final", "origin": final.origin, "accepted": final.accepted,
        })
        return AgentResult(final.source, {
            "agent": "coordination-v1",
            "arm": config.models,
            "origin": final.origin,
            "accepted_by_repl": final.accepted,
            "stages": stage_log,
            "wall_s": round(time.monotonic() - deadline.started, 1),
        })

    async def _concretize_exact(self, challenge, accepted_candidate, check, record):
        """Replace a successful `exact?` with its concrete `Try this` suggestion."""

        for message in accepted_candidate.messages:
            match = TRY_THIS_RE.search(str(message.get("data", "")))
            if not match:
                continue
            suggestion = match.group(1).strip()
            source = splice_tactics(challenge, suggestion)
            if source is None:
                continue
            candidate = Candidate(source=source, origin=f"sweep:exact?→{suggestion[:40]}")
            await check(candidate, timeout_s=60)
            record(candidate, "S0")
            if candidate.accepted:
                return candidate
        return None

    # ------------------------------------------------------------------
    # S1: pooled diverse sampling; S2: short error-informed repair

    async def _llm_stages(self, problem, services, parsed, config, deadline,
                          check, record, stage_log):
        semaphore = asyncio.Semaphore(config.llm_concurrency)

        async def sample(model: str, prompt_messages, *, max_tokens, temperature,
                         reasoning, timeout_s) -> str | None:
            async with semaphore:
                if not deadline.allows(timeout_s + 30):
                    return None
                response = await services.llm.complete(
                    model=model, messages=prompt_messages, max_tokens=max_tokens,
                    temperature=temperature, reasoning=reasoning, timeout_s=timeout_s,
                )
                if response.finish_reason == "error" or not response.content:
                    return None  # provider hiccup (for example content filter); one sample wasted
                return response.content

        def build_messages(feedback: str = "") -> list[dict[str, str]]:
            system = (
                "You are an expert in Lean 4 and Mathlib writing a complete, compiling Lean file.\n"
                "Rules:\n"
                "- Return ONE complete Lean file in a single ```lean code block.\n"
                "- Start from the exact challenge below. Keep every theorem/abbrev statement "
                "byte-for-byte identical; only replace each `sorry`.\n"
                "- Never use sorry, admit, axiom, or native_decide (plain decide is fine).\n"
                "- Numeric answer abbrevs (`abbrev … : ℕ :=`) must be plain decimal literals.\n"
                "- Use Lean 4 / current Mathlib syntax (omega, norm_num, nlinarith, simp, "
                "interval_cases, Nat.pow_mod, push_cast…). Helper lemmas above the theorem are fine.\n"
                "- Prefer short robust tactic proofs. If a computation is heavy, consider "
                "`set_option maxHeartbeats 1000000` / `set_option exponentiation.threshold 10000`."
            )
            user_parts = [
                f"Problem {problem.id}:", problem.description, "",
                "Challenge file (fill in the sorries, change nothing else):",
                "```lean", problem.challenge.rstrip(), "```",
            ]
            if feedback:
                user_parts += ["", "Lean compiler feedback on the previous attempt:",
                               "```", feedback, "```",
                               "Fix the reported problems. Return the full corrected file."]
            return [{"role": "system", "content": system},
                    {"role": "user", "content": "\n".join(user_parts)}]

        arm = config.models
        plans: list[tuple[str, dict]] = []
        if arm in ("duo", "qwen"):
            count = config.qwen_samples if arm == "duo" else config.qwen_samples + config.gptoss_samples
            plans += [(QWEN, dict(max_tokens=16000, temperature=0.8, reasoning=None,
                                  timeout_s=int(config.qwen_call_s)))] * count
        if arm in ("duo", "gptoss"):
            count = config.gptoss_samples if arm == "duo" else config.qwen_samples + config.gptoss_samples
            plans += [(GPTOSS, dict(max_tokens=24000, temperature=1.0,
                                    reasoning={"effort": "medium"},
                                    timeout_s=int(config.gptoss_call_s)))] * count

        texts = await asyncio.gather(
            *(sample(model, build_messages(), **kwargs) for model, kwargs in plans),
            return_exceptions=True,
        )
        for exc in (t for t in texts if isinstance(t, BaseException)):
            raise exc

        candidates: list[Candidate] = []
        seen: set[str] = set()
        for (model, _), text in zip(plans, texts):
            source = extract_lean(text) if isinstance(text, str) else None
            if not source:
                continue
            guarded, _reason = guard_candidate(source, parsed, parsed.imports)
            if not guarded or guarded in seen:
                continue
            seen.add(guarded)
            tag = "qwen" if model == QWEN else "gptoss"
            candidates.append(Candidate(source=guarded, origin=f"{tag}:s1"))
        stage_log.append({"stage": "S1", "planned": len(plans), "usable": len(candidates)})

        for candidate in candidates:
            if not deadline.allows(120):
                return None
            await check(candidate, timeout_s=90)
            record(candidate, "S1")
            if candidate.accepted:
                return candidate

        # ---- S2: short repair on the nearest misses ----------------------
        candidates.sort(key=lambda c: c.error_count)
        for candidate in candidates[:2]:
            feedback_source = candidate
            model = QWEN if candidate.origin.startswith("qwen") else GPTOSS
            if arm == "qwen":
                model = QWEN
            if arm == "gptoss":
                model = GPTOSS
            for round_index in range(config.repair_rounds):
                fixed = self._deterministic_fixes(feedback_source)
                if fixed is not None:
                    await check(fixed, timeout_s=90)
                    record(fixed, "S2")
                    if fixed.accepted:
                        return fixed
                    feedback_source = min(feedback_source, fixed, key=lambda c: c.error_count)
                call_s = config.qwen_call_s if model == QWEN else config.gptoss_call_s
                if not deadline.allows(call_s + 150):
                    return None
                feedback = format_messages(feedback_source.messages)
                text = await sample(
                    model, build_messages(feedback),
                    max_tokens=16000 if model == QWEN else 24000,
                    temperature=0.3 if model == QWEN else 1.0,
                    reasoning=None if model == QWEN else {"effort": "medium"},
                    timeout_s=int(call_s),
                )
                source = extract_lean(text) if text else None
                guarded = guard_candidate(source, parsed, parsed.imports)[0] if source else None
                if not guarded:
                    continue
                repaired = Candidate(
                    source=guarded,
                    origin=f"{'qwen' if model == QWEN else 'gptoss'}:s2:r{round_index + 1}",
                )
                await check(repaired, timeout_s=90)
                record(repaired, "S2")
                if repaired.accepted:
                    return repaired
                feedback_source = repaired
        stage_log.append({"stage": "S2", "solved": False})
        return None

    def _deterministic_fixes(self, candidate: Candidate) -> Candidate | None:
        """Free error->fix rules: kernel limits show up as specific messages."""

        text = " ".join(str(m.get("data", "")) for m in candidate.messages)
        preamble_lines = []
        if "exceeds the threshold" in text and "exponentiation.threshold" not in candidate.source:
            preamble_lines.append("set_option exponentiation.threshold 10000")
        if "maximum recursion depth" in text and "maxRecDepth" not in candidate.source:
            preamble_lines.append("set_option maxRecDepth 8000")
        if ("maximum number of heartbeats" in text or "deterministic) timeout" in text) \
                and "maxHeartbeats" not in candidate.source:
            preamble_lines.append("set_option maxHeartbeats 1000000")
        if not preamble_lines:
            return None
        return Candidate(
            source=insert_preamble(candidate.source, "\n".join(preamble_lines)),
            origin=candidate.origin + "+setopt",
        )


def format_messages(messages: list[dict[str, Any]], limit: int = 5000) -> str:
    chunks = []
    for message in messages:
        if message.get("severity") not in ("error", "warning"):
            continue
        chunks.append(f"{message.get('severity')} at {message.get('pos')}: "
                      f"{str(message.get('data', '')).strip()}")
    return "\n\n".join(chunks)[-limit:]


def create_agent() -> SubmissionAgent:
    return SubmissionAgent()
