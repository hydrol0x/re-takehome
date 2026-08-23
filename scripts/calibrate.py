"""Cheap calibration probes for the two pinned models (run locally with the key).

Answers, for ~$0.10 total:
  1. Does qwen3.5-flash thinking mode engage via `reasoning: {enabled}/{max_tokens}/{effort}`
     through OpenRouter, and what does it cost / how long does it take?
  2. What do gpt-oss-120b effort levels cost in latency, reasoning tokens, and dollars
     under this harness's provider constraints (price-ceiling tier, no provider pinning)?
  3. Do both models return a clean ```lean fenced block when asked?

Usage:
    .venv/bin/python scripts/calibrate.py            # all probes (~$0.05-0.15)
    .venv/bin/python scripts/calibrate.py --quick    # skip the Lean-format probes

Writes a summary table to stdout and full JSON to calibration-<timestamp>.json
(gitignored via outputs pattern? no — written to ./outputs/, which is fine to
inspect and is not auto-committed). Never prints the API key.
"""

from __future__ import annotations

import argparse
import asyncio
import json
import time
from datetime import UTC, datetime
from pathlib import Path

from re_harness.budget import BudgetLedger
from re_harness.config import HarnessSettings
from re_harness.events import EventLogger
from re_harness.llm import LLMCallError, LLMClient
from re_harness.models import MODEL_A as QWEN, MODEL_B as GPTOSS

DEV_PROXY_CA = "/root/.ccr/ca-bundle.crt"


def dev_transport():
    """httpx transport for the Claude-web dev container's egress proxy.

    That container only allows outbound HTTPS through a TLS-re-terminating
    proxy, which the harness client (trust_env=False) would bypass. LLMClient
    officially accepts a `transport`, so we inject one that uses the proxy and
    trusts its CA — TLS verification stays enabled. Returns None everywhere
    else (judge environment, local machines), leaving harness behavior
    untouched.
    """

    import os as _os
    proxy = _os.environ.get("HTTPS_PROXY")
    if not (proxy and Path(DEV_PROXY_CA).exists()):
        return None
    import ssl

    import certifi
    import httpx
    ctx = ssl.create_default_context(cafile=certifi.where())
    ctx.load_verify_locations(DEV_PROXY_CA)
    return httpx.AsyncHTTPTransport(proxy=proxy, verify=ctx)

MATH_PROMPT = (
    "Compute 7^2026 mod 100. Think it through, then end with exactly one line: "
    "ANSWER: <number>"
)
LEAN_PROMPT = (
    "Write a complete Lean 4 file using Mathlib that proves: for real numbers a b, "
    "a^2 + b^2 >= 2*a*b. Name the theorem sq_ge. Return only one ```lean code block."
)

PROBES = [
    # (label, model, prompt, kwargs)
    ("qwen default (control)", QWEN, MATH_PROMPT,
     dict(max_tokens=3000, temperature=0.7)),
    ("qwen reasoning enabled", QWEN, MATH_PROMPT,
     dict(max_tokens=12000, temperature=0.7, reasoning={"enabled": True})),
    ("qwen reasoning budget 4k", QWEN, MATH_PROMPT,
     dict(max_tokens=12000, temperature=0.7, reasoning={"enabled": True, "max_tokens": 4000})),
    ("qwen effort high", QWEN, MATH_PROMPT,
     dict(max_tokens=12000, temperature=0.7, reasoning={"effort": "high"})),
    ("gptoss effort low", GPTOSS, MATH_PROMPT,
     dict(max_tokens=8000, temperature=1.0, reasoning={"effort": "low"})),
    ("gptoss effort medium", GPTOSS, MATH_PROMPT,
     dict(max_tokens=12000, temperature=1.0, reasoning={"effort": "medium"})),
    ("gptoss effort high", GPTOSS, MATH_PROMPT,
     dict(max_tokens=20000, temperature=1.0, reasoning={"effort": "high"})),
]
LEAN_PROBES = [
    ("qwen lean format", QWEN, LEAN_PROMPT,
     dict(max_tokens=8000, temperature=0.3)),
    ("gptoss lean format", GPTOSS, LEAN_PROMPT,
     dict(max_tokens=12000, temperature=1.0, reasoning={"effort": "medium"})),
]


async def run_probe(llm: LLMClient, label: str, model: str, prompt: str, kwargs: dict) -> dict:
    started = time.monotonic()
    row: dict = {"label": label, "model": model, "request": {k: v for k, v in kwargs.items()}}
    try:
        response = await llm.complete(
            model=model,
            messages=[{"role": "user", "content": prompt}],
            timeout_s=900,
            **kwargs,
        )
    except LLMCallError as exc:
        row.update(status="TRANSPORT-ERROR (ledger closed!)", error=str(exc)[:200])
        return row
    usage = response.usage or {}
    details = usage.get("completion_tokens_details") or {}
    content = response.content or ""
    answer = None
    for line in reversed(content.strip().splitlines()):
        if line.strip().upper().startswith("ANSWER:"):
            answer = line.split(":", 1)[1].strip()
            break
    row.update(
        status="ok",
        latency_s=round(time.monotonic() - started, 1),
        finish=response.finish_reason,
        prompt_tokens=usage.get("prompt_tokens"),
        completion_tokens=usage.get("completion_tokens"),
        reasoning_tokens=details.get("reasoning_tokens"),
        cost_usd=usage.get("cost"),
        reasoning_returned=bool(response.reasoning),
        has_lean_fence="```lean" in content,
        answer=answer,
        content_head=content[:120].replace("\n", " "),
    )
    return row


async def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--quick", action="store_true", help="skip Lean-format probes")
    parser.add_argument("--cap-usd", type=float, default=0.30)
    args = parser.parse_args()

    settings = HarnessSettings.from_env(n_workers=1)
    if not settings.api_key:
        print("OPENROUTER_API_KEY is not set (.env or environment). Aborting without spend.")
        return 1

    out_dir = Path("outputs")
    out_dir.mkdir(exist_ok=True)
    stamp = datetime.now(UTC).strftime("%Y%m%dT%H%M%SZ")
    events = EventLogger(out_dir / f"calibration-{stamp}.events.jsonl",
                         problem_id="calibration", secrets=(settings.api_key,))
    budget = BudgetLedger(args.cap_usd)
    llm = LLMClient(api_key=settings.api_key, budget=budget, events=events,
                    transport=dev_transport())

    rows = []
    probes = PROBES + ([] if args.quick else LEAN_PROBES)
    try:
        # Serial on purpose: latency numbers stay clean and one transport error
        # cannot strand several in-flight reservations.
        for label, model, prompt, kwargs in probes:
            print(f"probe: {label} ...", flush=True)
            row = await run_probe(llm, label, model, prompt, kwargs)
            rows.append(row)
            if "ledger closed" in row.get("status", ""):
                print("  transport error closed the ledger; stopping probes.")
                break
    finally:
        await llm.aclose()

    header = f"{'probe':26s} {'lat s':>6s} {'out tok':>8s} {'think':>7s} {'cost $':>9s} {'fin':>7s}  answer/fence"
    print("\n" + header)
    print("-" * len(header))
    total = 0.0
    for row in rows:
        if row.get("status") != "ok":
            print(f"{row['label']:26s} {row.get('status')}: {row.get('error', '')[:60]}")
            continue
        total += row.get("cost_usd") or 0.0
        extra = row.get("answer") or ("lean-fence" if row.get("has_lean_fence") else "-")
        print(f"{row['label']:26s} {row['latency_s']:6.1f} {row['completion_tokens'] or 0:8d} "
              f"{row['reasoning_tokens'] or 0:7d} {row['cost_usd'] or 0:9.5f} "
              f"{str(row['finish']):>7s}  {extra}")
    print(f"\ntotal spend: ${total:.4f}  (cap ${args.cap_usd:.2f})")
    report = out_dir / f"calibration-{stamp}.json"
    report.write_text(json.dumps(rows, indent=2))
    print(f"full report: {report}")
    print("note: 7^2026 mod 100 = 49 — check the answer column for correctness.")
    return 0


if __name__ == "__main__":
    raise SystemExit(asyncio.run(main()))
