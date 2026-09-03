"""Offline Lean checker for reference proofs and custom challenges.

Usage:
    .venv/bin/python scripts/check_lean.py FILE [FILE ...]
        REPL-check each file (full Mathlib env); prints OK or the errors.

    .venv/bin/python scripts/check_lean.py --compare CHALLENGE SOLUTION \
        --theorems name1,name2 [--defs name1,name2]
        Run the real comparator (pristine challenge build + kernel-level
        statement equality + axiom audit) — what judging actually does.

Requires docker + the pinned Lean image (run scripts/setup.sh first).
"""

from __future__ import annotations

import argparse
import asyncio
import sys
import uuid
from pathlib import Path

from re_harness.config import HarnessSettings
from re_harness.events import EventLogger
from re_harness.lean import LeanClient, compare_solution
from re_harness.manifest import ProblemSpec


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("files", nargs="*", type=Path)
    parser.add_argument("--compare", nargs=2, type=Path, metavar=("CHALLENGE", "SOLUTION"))
    parser.add_argument("--theorems", default="")
    parser.add_argument("--defs", default="")
    parser.add_argument("--timeout", type=int, default=300)
    args = parser.parse_args()
    settings = HarnessSettings.from_env(n_workers=1)

    if args.compare:
        challenge, solution = (p.read_text() for p in args.compare)
        spec = ProblemSpec(
            id=args.compare[0].stem,
            theorem_names=tuple(n for n in args.theorems.split(",") if n),
            definition_names=tuple(n for n in args.defs.split(",") if n),
            numeric_answer_names=(),
            metadata={},
        )
        result = compare_solution(
            image=settings.lean_image, session_id=uuid.uuid4().hex,
            challenge=challenge, solution=solution, spec=spec,
            timeout_s=args.timeout,
        )
        print(f"comparator passed={result.passed} exit={result.exit_code} "
              f"timed_out={result.timed_out} duration_ms={result.duration_ms}")
        stdout = str(result.output.get("stdout") or result.output.get("error") or "")
        print(stdout[-3000:])
        return 0 if result.passed else 1

    if not args.files:
        parser.error("pass files to REPL-check, or --compare")
    events = EventLogger(Path("outputs/check-lean.events.jsonl"), problem_id="check")
    client = LeanClient(image=settings.lean_image, events=events)
    failures = 0
    try:
        for path in args.files:
            check = asyncio.run(client.check_file(path.read_text(), timeout_s=args.timeout))
            errors = [m for m in check.messages if m.get("severity") == "error"]
            sorries = [m for m in check.messages
                       if "declaration uses `sorry`" in str(m.get("data", ""))]
            if check.timed_out:
                print(f"TIMEOUT {path}")
                failures += 1
            elif errors:
                print(f"FAIL    {path} ({len(errors)} errors)")
                for m in errors[:6]:
                    print(f"        {m.get('pos')}: {str(m.get('data'))[:180]}")
                failures += 1
            else:
                tag = f" ({len(sorries)} sorries)" if sorries else ""
                print(f"OK      {path}{tag}")
    finally:
        client.close()
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
