from __future__ import annotations

import json
import asyncio

import httpx
import pytest

from re_harness.budget import BudgetAccountingError, BudgetLedger
from re_harness.events import EventLogger
from re_harness.llm import LLMCallError, LLMClient, LLMPolicyError
from re_harness.models import MODEL_A


@pytest.mark.asyncio
async def test_logged_openrouter_call_uses_actual_cost_and_no_secret(tmp_path):
    key = "super-secret-key"

    def handler(request: httpx.Request) -> httpx.Response:
        assert request.url == httpx.URL("https://openrouter.ai/api/v1/chat/completions")
        assert request.headers["authorization"] == f"Bearer {key}"
        body = json.loads(request.content)
        assert "plugins" not in body
        assert body["provider"] == {
            "allow_fallbacks": True,
            "require_parameters": True,
            "max_price": {"prompt": 0.15, "completion": 0.60},
        }
        return httpx.Response(200, json={
            "id": "gen-1",
            "model": MODEL_A,
            "choices": [{
                "finish_reason": "stop",
                "message": {"content": f"answer {key}", "reasoning": "because"},
            }],
            "usage": {
                "prompt_tokens": 10,
                "completion_tokens": 5,
                "total_tokens": 15,
                "cost": 0.0123,
            },
        })

    events_path = tmp_path / "events.jsonl"
    ledger = BudgetLedger(1.0)
    client = LLMClient(
        api_key=key,
        budget=ledger,
        events=EventLogger(events_path, problem_id="p", secrets=(key,)),
        transport=httpx.MockTransport(handler),
    )
    response = await client.complete(
        model=MODEL_A,
        messages=[{"role": "user", "content": f"say {key}"}],
        max_tokens=100,
    )
    await client.aclose()
    assert response.content == f"answer {key}"
    assert ledger.snapshot().spent_usd == pytest.approx(0.0123)
    assert key not in events_path.read_text()


@pytest.mark.asyncio
async def test_model_suffix_is_rejected_before_transport(tmp_path):
    def handler(_request):
        raise AssertionError("transport should not be called")

    client = LLMClient(
        api_key="key",
        budget=BudgetLedger(1),
        events=EventLogger(tmp_path / "events", problem_id="p"),
        transport=httpx.MockTransport(handler),
    )
    with pytest.raises(LLMPolicyError):
        await client.complete(
            model=MODEL_A + ":online", messages=[{"role": "user", "content": "x"}]
        )
    with pytest.raises(TypeError):
        await client.complete(
            model=MODEL_A,
            messages=[{"role": "user", "content": "x"}],
            plugins=[{"id": "web"}],  # type: ignore[call-arg]
        )
    with pytest.raises(LLMPolicyError, match="must be text"):
        await client.complete(
            model=MODEL_A,
            messages=[{"role": "user", "content": [{"type": "image_url", "image_url": "x"}]}],
        )
    await client.aclose()


@pytest.mark.asyncio
async def test_missing_cost_disables_future_calls(tmp_path):
    def handler(_request):
        return httpx.Response(200, json={
            "id": "gen",
            "choices": [{"finish_reason": "stop", "message": {"content": "x"}}],
            "usage": {"prompt_tokens": 1, "completion_tokens": 1},
        })

    client = LLMClient(
        api_key="key",
        budget=BudgetLedger(1),
        events=EventLogger(tmp_path / "events", problem_id="p"),
        transport=httpx.MockTransport(handler),
    )
    with pytest.raises(LLMCallError):
        await client.complete(model=MODEL_A, messages=[{"role": "user", "content": "x"}])
    with pytest.raises(BudgetAccountingError):
        await client.complete(model=MODEL_A, messages=[{"role": "user", "content": "x"}])
    await client.aclose()


@pytest.mark.asyncio
async def test_http_error_releases_budget_and_allows_retry(tmp_path):
    calls = []

    def handler(_request):
        calls.append(1)
        if len(calls) == 1:
            return httpx.Response(429, text="limited")
        return httpx.Response(200, json={
            "id": "gen-2",
            "model": MODEL_A,
            "choices": [{"finish_reason": "stop", "message": {"content": "ok"}}],
            "usage": {"prompt_tokens": 1, "completion_tokens": 1, "cost": 0.001},
        })

    ledger = BudgetLedger(1)
    client = LLMClient(
        api_key="key",
        budget=ledger,
        events=EventLogger(tmp_path / "events", problem_id="p"),
        transport=httpx.MockTransport(handler),
    )
    # Kit PR #5 semantics: an HTTP error status is a zero-cost refusal, so the
    # reservation is released, the ledger stays open, and a retry can settle.
    with pytest.raises(LLMCallError, match="no spend was recorded"):
        await client.complete(model=MODEL_A, messages=[{"role": "user", "content": "x"}])
    snapshot = ledger.snapshot()
    assert snapshot.accounting_complete
    assert snapshot.reserved_usd == 0
    assert snapshot.spent_usd == 0
    response = await client.complete(
        model=MODEL_A, messages=[{"role": "user", "content": "x"}]
    )
    assert response.content == "ok"
    assert ledger.snapshot().spent_usd == pytest.approx(0.001)
    await client.aclose()


@pytest.mark.asyncio
async def test_transport_failure_defaults_to_fail_closed(tmp_path, monkeypatch):
    monkeypatch.delenv("VM_TRANSPORT_FAILURE_POLICY", raising=False)

    def handler(_request):
        raise httpx.ConnectError("connection dropped")

    ledger = BudgetLedger(1)
    client = LLMClient(
        api_key="key",
        budget=ledger,
        events=EventLogger(tmp_path / "events", problem_id="p"),
        transport=httpx.MockTransport(handler),
    )
    with pytest.raises(LLMCallError, match="spend is uncertain"):
        await client.complete(model=MODEL_A, messages=[{"role": "user", "content": "x"}])
    assert not ledger.snapshot().accounting_complete
    await client.aclose()


@pytest.mark.asyncio
async def test_transport_release_policy_keeps_ledger_open(tmp_path, monkeypatch):
    # Dev-container knob only (container restarts chop in-flight connections);
    # never set during judging, where the default above applies.
    monkeypatch.setenv("VM_TRANSPORT_FAILURE_POLICY", "release")
    calls = []

    def handler(_request):
        calls.append(1)
        if len(calls) == 1:
            raise httpx.ConnectError("connection dropped")
        return httpx.Response(200, json={
            "id": "gen-3",
            "model": MODEL_A,
            "choices": [{"finish_reason": "stop", "message": {"content": "ok"}}],
            "usage": {"prompt_tokens": 1, "completion_tokens": 1, "cost": 0.002},
        })

    ledger = BudgetLedger(1)
    client = LLMClient(
        api_key="key",
        budget=ledger,
        events=EventLogger(tmp_path / "events", problem_id="p"),
        transport=httpx.MockTransport(handler),
    )
    with pytest.raises(LLMCallError, match="reservation released"):
        await client.complete(model=MODEL_A, messages=[{"role": "user", "content": "x"}])
    snapshot = ledger.snapshot()
    assert snapshot.accounting_complete
    assert snapshot.reserved_usd == 0
    response = await client.complete(
        model=MODEL_A, messages=[{"role": "user", "content": "x"}]
    )
    assert response.content == "ok"
    assert ledger.snapshot().spent_usd == pytest.approx(0.002)
    await client.aclose()


@pytest.mark.asyncio
async def test_cancelled_inflight_call_fails_budget_closed(tmp_path):
    entered = asyncio.Event()

    async def handler(_request):
        entered.set()
        await asyncio.Event().wait()

    ledger = BudgetLedger(1)
    client = LLMClient(
        api_key="key",
        budget=ledger,
        events=EventLogger(tmp_path / "events", problem_id="p"),
        transport=httpx.MockTransport(handler),
    )
    task = asyncio.create_task(
        client.complete(model=MODEL_A, messages=[{"role": "user", "content": "x"}])
    )
    await entered.wait()
    task.cancel()
    with pytest.raises(asyncio.CancelledError):
        await task
    assert not ledger.snapshot().accounting_complete
    await client.aclose()
