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
BANNED_RE = re.compile(
    r"(?<![A-Za-z0-9_'])(sorry|admit|native_decide|sorryAx)(?![A-Za-z0-9_'])|^\s*axiom\s",
    re.MULTILINE,
)
SKETCH_BANNED_RE = re.compile(  # sorry allowed in sketches, escapes still banned
    r"(?<![A-Za-z0-9_'])(admit|native_decide|sorryAx)(?![A-Za-z0-9_'])|^\s*axiom\s",
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
    if "import " not in candidate:
        candidate = "\n".join(parsed.imports) + "\n\n" + candidate
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


def error_signature(messages: list[dict[str, Any]]) -> str:
    """Stable fingerprint of the error pattern, for plateau detection."""

    heads = sorted(
        str(m.get("data", "")).strip().splitlines()[0][:80]
        for m in messages
        if m.get("severity") == "error"
    )
    return hashlib.sha256("\n".join(heads).encode()).hexdigest()[:16]
