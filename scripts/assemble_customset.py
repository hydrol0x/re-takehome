"""Assemble authored custom problems into eval-set directories.

Usage:
  .venv/bin/python scripts/assemble_customset.py SRC_DIR... --dev OUT1 --held OUT2 \
      --held-ids id1,id2,...

Each SRC_DIR contains per-problem directories with challenge.lean,
problem.md, reference.lean, manifest.json. Problems named in --held-ids go
to the held set, the rest to dev. Reference proofs are copied to
reference-custom/<id>.lean (repo-side truth certificates, never read by the
agent). Re-validate with scripts/check_lean.py before trusting the output.
"""

from __future__ import annotations

import argparse
import json
import shutil
from pathlib import Path

REQUIRED = ("challenge.lean", "problem.md", "reference.lean", "manifest.json")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("sources", nargs="+", type=Path)
    parser.add_argument("--dev", type=Path, required=True)
    parser.add_argument("--held", type=Path, required=True)
    parser.add_argument("--held-ids", default="")
    parser.add_argument("--refs", type=Path, default=Path("reference-custom"))
    args = parser.parse_args()
    held_ids = {i for i in args.held_ids.split(",") if i}

    problems = []
    for src in args.sources:
        for pdir in sorted(p for p in src.iterdir() if p.is_dir()):
            missing = [f for f in REQUIRED if not (pdir / f).is_file()]
            if missing:
                print(f"SKIP {pdir.name}: missing {missing}")
                continue
            spec = json.loads((pdir / "manifest.json").read_text())
            if spec.get("id") != pdir.name:
                print(f"SKIP {pdir.name}: manifest id mismatch ({spec.get('id')})")
                continue
            challenge = (pdir / "challenge.lean").read_text()
            if not challenge.startswith("import Mathlib\n"):
                print(f"SKIP {pdir.name}: challenge must start with 'import Mathlib'")
                continue
            problems.append((pdir, spec))

    for out_dir, wanted in ((args.dev, False), (args.held, True)):
        chosen = [(p, s) for p, s in problems if (s["id"] in held_ids) == wanted]
        out_dir.mkdir(parents=True, exist_ok=True)
        manifest = {"schema_version": 1, "set": out_dir.name, "problems": []}
        for pdir, spec in chosen:
            dest = out_dir / spec["id"]
            dest.mkdir(exist_ok=True)
            shutil.copy(pdir / "challenge.lean", dest / "challenge.lean")
            shutil.copy(pdir / "problem.md", dest / "problem.md")
            manifest["problems"].append({
                "id": spec["id"],
                "theorem_names": spec.get("theorem_names", []),
                "definition_names": spec.get("definition_names", []),
                "numeric_answer_names": spec.get("numeric_answer_names", []),
            })
        (out_dir / "manifest.json").write_text(json.dumps(manifest, indent=1) + "\n")
        print(f"{out_dir}: {len(chosen)} problems")

    args.refs.mkdir(exist_ok=True)
    for pdir, spec in problems:
        shutil.copy(pdir / "reference.lean", args.refs / f"{spec['id']}.lean")
    print(f"{args.refs}: {len(problems)} reference proofs")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
