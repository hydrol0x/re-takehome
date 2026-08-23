"""Compare one or more run directories: scores, origins, spend, overlap.

Usage:
    .venv/bin/python scripts/analyze_runs.py LABEL=RUN_DIR [LABEL=RUN_DIR ...]

Example:
    .venv/bin/python scripts/analyze_runs.py \
        duo=outputs/submission/20260823T002337Z \
        qwen=outputs/submission/20260823T0430Z
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

UNSCORABLE = {"rmo_2000_3", "rmo_2000_6"}  # see reference/README.md


def load_run(run_dir: Path) -> dict[str, dict]:
    problems: dict[str, dict] = {}
    for result_path in sorted(run_dir.glob("*/result.json")):
        data = json.loads(result_path.read_text())
        meta = data.get("agent_metadata") or {}
        problems[data["problem_id"]] = {
            "passed": bool(data.get("passed")),
            "status": data.get("status"),
            "origin": meta.get("origin", "?"),
            "arm": meta.get("arm", "?"),
            "spend": float((data.get("budget") or {}).get("spent_usd") or 0.0),
            "wall_s": float(data.get("wall_s") or 0.0),
            "both_models": bool(data.get("both_required_models_used")),
        }
    return problems


def main() -> int:
    runs: dict[str, dict[str, dict]] = {}
    for arg in sys.argv[1:]:
        label, _, path = arg.partition("=")
        if not path:
            label, path = Path(arg).name, arg
        runs[label] = load_run(Path(path))
    if not runs:
        print(__doc__)
        return 1

    all_problems = sorted({p for r in runs.values() for p in r})
    labels = list(runs)

    header = f"{'problem':22s}" + "".join(f"{label:>26s}" for label in labels)
    print(header)
    print("-" * len(header))
    for problem in all_problems:
        row = f"{problem:22s}"
        if problem in UNSCORABLE:
            row = f"{problem + ' (unscorable)':22s}"
        for label in labels:
            info = runs[label].get(problem)
            if info is None:
                cell = "—"
            else:
                mark = "PASS" if info["passed"] else info["status"][:9]
                cell = f"{mark} {info['origin'][:14]} ${info['spend']:.3f}"
            row += f"{cell:>26s}"
        print(row)

    print()
    for label in labels:
        run = runs[label]
        solved = {p for p, i in run.items() if i["passed"]}
        spend = sum(i["spend"] for i in run.values())
        wall = sum(i["wall_s"] for i in run.values())
        both = sum(1 for i in run.values() if i["both_models"])
        print(f"{label:12s} solved {len(solved):2d}/{len(run)} "
              f"(scorable ceiling {len(run) - len(UNSCORABLE & set(run))}) "
              f"spend ${spend:.3f}  wall {wall/60:.0f} min  both-models on {both}")

    if len(labels) > 1:
        print()
        solved_sets = {label: {p for p, i in runs[label].items() if i["passed"]}
                       for label in labels}
        union = set().union(*solved_sets.values())
        inter = set.intersection(*solved_sets.values()) if solved_sets else set()
        print(f"union {len(union)} | intersection {len(inter)}")
        for label in labels:
            unique = solved_sets[label] - set().union(
                *(s for l, s in solved_sets.items() if l != label))
            if unique:
                print(f"only {label}: {sorted(unique)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
