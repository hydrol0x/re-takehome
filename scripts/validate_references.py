"""Validate every custom reference proof through the full Comparator gate.

Runs each reference-custom/<id>.lean against its pristine challenge with the
manifest's theorem/definition/answer names, in a fresh scoring container per
problem — the same gate that scores submissions. Writes a JSON summary.

    .venv/bin/python scripts/validate_references.py
"""
from __future__ import annotations

import json
import pathlib
import sys
import uuid

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "src"))

from re_harness.config import HarnessSettings
from re_harness.lean import compare_solution
from re_harness.manifest import ProblemSpec, load_problem_set

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = ROOT / "outputs" / "reference-comparator-validation.json"


def main() -> int:
    settings = HarnessSettings.from_env(n_workers=1)
    rows = []
    for set_dir in ("custom-problems-dev", "custom-problems-held"):
        pset = load_problem_set(ROOT / set_dir)
        for spec in pset.problems:
            ref = ROOT / "reference-custom" / f"{spec.id}.lean"
            challenge = (ROOT / set_dir / spec.id / "challenge.lean").read_text()
            if not ref.exists():
                rows.append({"id": spec.id, "set": set_dir, "status": "missing-reference"})
                print(f"{spec.id}: MISSING", flush=True)
                continue
            result = compare_solution(
                image=settings.lean_image,
                session_id=uuid.uuid4().hex,
                challenge=challenge,
                solution=ref.read_text(),
                spec=spec,
                timeout_s=600,
            )
            rows.append({
                "id": spec.id,
                "set": set_dir,
                "passed": result.passed,
                "exit_code": result.exit_code,
                "timed_out": result.timed_out,
                "duration_ms": result.duration_ms,
            })
            print(f"{spec.id}: passed={result.passed} timed_out={result.timed_out} "
                  f"dur={result.duration_ms}ms", flush=True)
    OUT.parent.mkdir(parents=True, exist_ok=True)
    OUT.write_text(json.dumps({"results": rows}, indent=2))
    n_pass = sum(1 for r in rows if r.get("passed"))
    print(f"TOTAL: {n_pass}/{len(rows)} comparator-passed -> {OUT}", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
