"""One tiny call per model through the patched client: does OpenRouter accept
allow_fallbacks:true under max_price, and does settle() still work? ~$0.001."""

import asyncio
import sys
from pathlib import Path

sys.path.insert(0, "scripts")
from calibrate import dev_transport  # noqa: E402

from re_harness.budget import BudgetLedger
from re_harness.config import HarnessSettings
from re_harness.events import EventLogger
from re_harness.llm import LLMClient
from re_harness.models import ALLOWED_MODELS


async def main() -> None:
    settings = HarnessSettings.from_env(n_workers=1)
    for model in sorted(ALLOWED_MODELS):
        ledger = BudgetLedger(0.05)
        client = LLMClient(
            api_key=settings.api_key,
            budget=ledger,
            events=EventLogger(Path("outputs/probe-patched.events.jsonl"), problem_id="probe"),
            transport=dev_transport(),
        )
        try:
            response = await client.complete(
                model=model,
                messages=[{"role": "user", "content": "Reply with the single word: ok"}],
                max_tokens=1024,
                timeout_s=120,
            )
            snap = ledger.snapshot()
            print(f"{model}: content={response.content.strip()[:40]!r} "
                  f"cost=${snap.spent_usd:.6f} complete={snap.accounting_complete}")
        finally:
            await client.aclose()


asyncio.run(main())
