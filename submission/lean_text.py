"""Pure text utilities for Lean challenge files: parsing, splicing, guards.

No harness or network dependencies — everything here is unit-testable offline.
"""

from __future__ import annotations

import ast
import hashlib
import re
from dataclasses import dataclass
from typing import Any

DECL_RE = re.compile(
    r"^(?P<indent>[ \t]*)(?P<kw>theorem|lemma|abbrev|def|instance)\s+(?P<name>[A-Za-z0-9_'.]+)",
    re.MULTILINE,
)
SORRY_RE = re.compile(r"(?<![A-Za-z0-9_'])sorry(?![A-Za-z0-9_'])")
_AXIOM_DECL = r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|unsafe\s+|scoped\s+)*axiom\s"
BANNED_RE = re.compile(
    r"(?<![A-Za-z0-9_'])(sorry|admit|native_decide|sorryAx)(?![A-Za-z0-9_'])|" + _AXIOM_DECL,
    re.MULTILINE,
)
SKETCH_BANNED_RE = re.compile(  # sorry allowed in sketches, escapes still banned
    r"(?<![A-Za-z0-9_'])(admit|native_decide|sorryAx)(?![A-Za-z0-9_'])|" + _AXIOM_DECL,
    re.MULTILINE,
)
FENCE_RE = re.compile(r"```(?:lean4?|Lean4?)?\s*\n(.*?)```", re.DOTALL)


@dataclass
class Hole:
    """One `sorry` occurrence."""

    start: int
    end: int
    indent: str
    is_tactic: bool  # preceded (modulo whitespace) by `by`; else a term hole
    decl_name: str = ""  # nearest enclosing declaration, best-effort


@dataclass
class Parsed:
    imports: list[str]
    holes: list[Hole]
    decl_names: list[str]
    signatures: list[str]  # normalized "kw name ... :=" per declaration
    numeric_answer_names: list[str]

    @property
    def has_term_holes(self) -> bool:
        return any(not hole.is_tactic for hole in self.holes)


def normalize_ws(text: str) -> str:
    return re.sub(r"\s+", " ", text).strip()


def parse_challenge(source: str) -> Parsed:
    imports = [line for line in source.splitlines() if line.startswith("import ")]
    decls = list(DECL_RE.finditer(source))
    holes: list[Hole] = []
    for match in SORRY_RE.finditer(source):
        before = source[: match.start()]
        line_start = before.rfind("\n") + 1
        indent = re.match(r"[ \t]*", source[line_start:]).group(0)
        stripped = before.rstrip()
        is_tactic = bool(re.search(r"\bby\b\s*$", stripped)) or not stripped.endswith(":=")
        owner = ""
        for decl in decls:
            if decl.start() <= match.start():
                owner = decl.group("name")
            else:
                break
        holes.append(Hole(match.start(), match.end(), indent, is_tactic, owner))
    signatures: list[str] = []
    numeric_answers: list[str] = []
    for i, decl in enumerate(decls):
        seg_end = decls[i + 1].start() if i + 1 < len(decls) else len(source)
        segment = source[decl.start(): seg_end]
        assign_at = segment.find(":=")
        if assign_at >= 0:
            signatures.append(normalize_ws(segment[: assign_at + 2]))
        if decl.group("kw") == "abbrev" and re.search(r":\s*(ℕ|Nat)\s*:=", segment):
            numeric_answers.append(decl.group("name"))
    return Parsed(imports, holes, [d.group("name") for d in decls], signatures, numeric_answers)


_BOUND_VAR = r"(?P<var>[A-Za-z_][A-Za-z0-9_']*)"
_BOUND_NUM = r"(?P<k>[0-9]+)"
_FORALL_RANGE_RE = re.compile(  # ∀ n ∈ Finset.range K,
    rf"∀\s*{_BOUND_VAR}\s*∈\s*Finset\.range\s+{_BOUND_NUM}\s*,")
_FORALL_BINDER_RE = re.compile(  # ∀ n < K,  /  ∀ n ≤ K,
    rf"∀\s*{_BOUND_VAR}\s*(?:<=|≤|<)\s*{_BOUND_NUM}\s*,")
_FORALL_ARROW_RE = re.compile(  # ∀ n, n < K →  /  ∀ n, n ≤ K →  (opt. : ℕ)
    rf"∀\s*{_BOUND_VAR}(?:\s*:\s*(?:ℕ|Nat))?\s*,\s*(?P=var)\s*(?:<=|≤|<)"
    rf"\s*{_BOUND_NUM}\s*(?:→|->)")


def bounded_intro_templates(decl_statement: str, max_bound: int = 300) -> list[str]:
    """Brute-force tactic scripts for statements led by a bounded universal.

    Given a declaration's statement text (up to `:=`, e.g. one entry of
    `Parsed.signatures`), detect a leading bounded `∀` of the forms
    `∀ n, n ≤ K →`, `∀ n, n < K →`, `∀ n ≤ K,`, `∀ n < K,` or
    `∀ n ∈ Finset.range K,` (arbitrary variable name; K a decimal numeral
    ≤ max_bound) and return deterministic intro + interval_cases scripts
    that can close such goals by exhaustion. Returns [] when no supported
    form leads the statement. Purely textual and best-effort: callers must
    verify the scripts — a false positive simply fails to check.
    """

    text = normalize_ws(decl_statement)
    at = text.find("∀")
    if at < 0:
        return []
    tail = text[at:]
    match = _FORALL_RANGE_RE.match(tail)
    is_range = match is not None
    if match is None:
        match = _FORALL_BINDER_RE.match(tail) or _FORALL_ARROW_RE.match(tail)
    if match is None or int(match.group("k")) > max_bound:
        return []
    var = match.group("var")
    intro = f"intro {var} h{var}"
    cases = f"interval_cases {var}"
    if is_range:
        unfold = f"simp only [Finset.mem_range] at h{var}"
        return [
            f"{intro}\n{unfold}\n{cases} <;> decide",
            f"{intro}\n{unfold}\n{cases} <;> omega",
            f"{intro}\n{unfold}\n{cases} <;> simp_all <;> omega",
        ]
    return [
        f"{intro}\n{cases} <;> omega",
        f"{intro}\n{cases} <;> decide",
        f"{intro}\n{cases} <;> simp_all <;> omega",
    ]


# ---------------------------------------------------------------------------
# Goal classification (SUBMISSION_TYPED_FILLS, research branch B4)

_INDUCTION_MARKERS_RE = re.compile(
    r"Nat\.rec|Nat\.factorial|Finset\.sum|Finset\.prod|∑|∏"
    r"|[A-Za-z0-9_'\)\]]\s*!(?!=)")  # factorial `n !`, not ASCII `!=`
_REL_CHARS = ("=", "≤", "<", "≥", ">")
_CAST_TYPES = ("ℕ", "ℤ", "ℝ")
_OPEN_BRACKETS, _CLOSE_BRACKETS = "([{⟨", ")]}⟩"


def _conclusion(text: str) -> str:
    """Best-effort conclusion of a statement: the segment after the first
    bracket-depth-0 `:` (past name and binders) and after the last depth-0
    `,`/`→`/`->` (past quantifier heads and hypotheses). Crude but pure."""

    depth = 0
    seen_colon = False
    cut = 0
    i = 0
    while i < len(text):
        char = text[i]
        if char in _OPEN_BRACKETS:
            depth += 1
        elif char in _CLOSE_BRACKETS:
            depth = max(0, depth - 1)
        elif depth == 0:
            if char == ":" and not seen_colon:
                seen_colon = True
                cut = i + 1
            elif char in ",→":
                cut = i + 1
            elif char == "-" and text.startswith("->", i):
                cut = i + 2
                i += 1
        i += 1
    return text[cut:]


def classify_goal(decl_statement: str) -> str:
    """Crude, deterministic goal class of one declaration statement.

    `decl_statement` is a statement's text up to `:=` (e.g. one entry of
    `Parsed.signatures`); bare goal text also works. Returns one of
    "induction", "divisibility", "cast", "inequality", "arith". Checks run
    most-specific-first, so listing order is precedence:
      induction     recursion/aggregation markers (Nat.rec, Nat.factorial,
                    Finset.sum/∑, Finset.prod/∏, factorial `!`), or a `∀ n`
                    over ℕ with the bound variable on both sides of an
                    equality/inequality;
      divisibility  `∣`, `Nat.gcd`, `Coprime`, or `% `;
      cast          two of ℕ/ℤ/ℝ mixed, or `↑`/`Nat.cast`/`Int.cast`
                    (checked before "inequality": a mixed-type relation
                    needs cast discipline first);
      inequality    ≤/</≥/> in the outermost relation position (i.e. in
                    the conclusion, past binders and hypotheses);
      arith         everything else.
    Purely textual: misclassification only costs prompt aptness.
    """

    text = re.sub(r":=\s*$", "", normalize_ws(decl_statement)).strip()
    if _INDUCTION_MARKERS_RE.search(text):
        return "induction"
    forall = re.search(r"∀\s*\(?\s*([A-Za-z_][A-Za-z0-9_']*)", text)
    if forall is not None and ("ℕ" in text or re.search(r"\bNat\b", text)):
        var_re = rf"(?<![A-Za-z0-9_']){re.escape(forall.group(1))}(?![A-Za-z0-9_'])"
        tail = text[forall.end():]
        for rel in _REL_CHARS:
            at = tail.find(rel)
            if at >= 0 and re.search(var_re, tail[:at]) \
                    and re.search(var_re, tail[at + 1:]):
                return "induction"
    if "∣" in text or "Nat.gcd" in text or "Coprime" in text or "% " in text:
        return "divisibility"
    if sum(marker in text for marker in _CAST_TYPES) >= 2 or "↑" in text \
            or "Nat.cast" in text or "Int.cast" in text:
        return "cast"
    if any(rel in _conclusion(text) for rel in ("≤", "<", "≥", ">")):
        return "inequality"
    return "arith"


def splice_holes(source: str, replacements: dict[int, str]) -> str:
    """Replace holes (by index into parse order) with tactic blocks."""

    parsed = parse_challenge(source)
    out: list[str] = []
    cursor = 0
    for index, hole in enumerate(parsed.holes):
        out.append(source[cursor: hole.start])
        if index in replacements:
            lines = replacements[index].splitlines() or [replacements[index]]
            out.append(("\n" + hole.indent).join(lines))
        else:
            out.append(source[hole.start: hole.end])
        cursor = hole.end
    out.append(source[cursor:])
    return "".join(out)


def splice_tactics(source: str, tactic: str, preamble: str = "") -> str | None:
    """Replace every tactic hole with `tactic`; None if any term hole exists."""

    parsed = parse_challenge(source)
    if not parsed.holes or parsed.has_term_holes:
        return None
    result = splice_holes(source, {i: tactic for i in range(len(parsed.holes))})
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


def extract_all_blocks(text: str) -> list[str]:
    """Every fenced lean block, stripped — for multi-candidate responses."""

    return [block.strip() for block in FENCE_RE.findall(text or "") if block.strip()]


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


def guard_candidate(
    candidate: str, parsed: Parsed, *, allow_sorry: bool = False
) -> tuple[str | None, str]:
    """Validate/normalize a model-written file. Returns (source, reject-reason)."""

    banned = SKETCH_BANNED_RE if allow_sorry else BANNED_RE
    if banned.search(candidate):
        return None, "contains a banned token (sorry/admit/native_decide/axiom)"
    # The scoring Comparator compares kernel-level statements, and a
    # statement can elaborate to a different term under a different import
    # set — so a model-added `import Mathlib.Tactic` on a minimal-import
    # challenge fails scoring even with a correct proof. The warm REPL strips
    # imports anyway; compose every candidate on the challenge's exact block.
    if parsed.imports:
        lines = candidate.splitlines()
        if [line for line in lines if line.startswith("import ")] != parsed.imports:
            body = [line for line in lines if not line.startswith("import ")]
            candidate = ("\n".join(parsed.imports) + "\n\n"
                         + "\n".join(body).lstrip("\n"))
    normalized = normalize_ws(candidate)
    for signature in parsed.signatures:
        if signature not in normalized:
            return None, f"statement altered or missing: {signature[:90]}"
    candidate = normalize_numeric_answers(candidate, parsed.numeric_answer_names)
    for name in parsed.numeric_answer_names:
        if not re.search(rf"\babbrev\s+{re.escape(name)}\s*:\s*(?:ℕ|Nat)\s*:=\s*[0-9]+\s*$",
                         candidate, re.MULTILINE):
            return None, f"numeric answer {name} is not a decimal literal"
    return candidate, ""


# Tactics that live in Mathlib.Tactic (not Lean core / Std) and therefore do
# not exist under a challenge that imports only a few Mathlib modules. The
# list is deliberately conservative: only tactics that are unambiguously
# Mathlib-provided, so the lint never rejects a core-only proof.
MATHLIB_ONLY_TACTICS = (
    "norm_num", "linarith", "nlinarith", "positivity", "polyrith", "field_simp",
    "ring_nf", "ring", "interval_cases", "fin_cases", "aesop", "gcongr", "tauto",
    "push_cast", "zify", "qify", "rify", "linear_combination", "nlinarith!",
    "bound", "norm_cast", "exact_mod_cast", "simp_arith", "use",
)
_MATHLIB_ONLY_RE = re.compile(
    r"(?<![A-Za-z0-9_.'])(" + "|".join(
        re.escape(name) for name in sorted(MATHLIB_ONLY_TACTICS, key=len, reverse=True))
    + r")(?![A-Za-z0-9_'])"
)


def surface_lint(source: str) -> str:
    """Name the first Mathlib-only tactic used outside comments, or ''."""

    stripped = "\n".join(line.split("--", 1)[0] for line in source.splitlines())
    match = _MATHLIB_ONLY_RE.search(stripped)
    return match.group(1) if match else ""


def format_messages(messages: list[dict[str, Any]], limit: int = 5000) -> str:
    chunks = []
    for message in messages:
        if message.get("severity") not in ("error", "warning"):
            continue
        data = str(message.get("data", "")).strip()
        if "declaration uses `sorry`" in data or "push_neg" in data:
            continue  # noise for repair purposes
        chunks.append(f"{message.get('severity')} at {message.get('pos')}: {data}")
    return "\n\n".join(chunks)[-limit:]


PERMITTED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def axiom_violations(messages: list[dict[str, Any]]) -> list[str]:
    """Parse `#print axioms` info output; return any non-permitted axioms."""

    bad: list[str] = []
    for message in messages:
        data = str(message.get("data", ""))
        if "depends on axioms:" not in data:
            continue
        listed = re.findall(r"[\[,]\s*([A-Za-z0-9_'.]+)", data.split("depends on axioms:", 1)[1])
        bad.extend(name for name in listed if name not in PERMITTED_AXIOMS)
    return bad


def error_signature(messages: list[dict[str, Any]]) -> str:
    """Stable fingerprint of the error pattern, for plateau detection."""

    heads = sorted(
        str(m.get("data", "")).strip().splitlines()[0][:80]
        for m in messages
        if m.get("severity") == "error"
    )
    return hashlib.sha256("\n".join(heads).encode()).hexdigest()[:16]
