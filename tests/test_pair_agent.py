from __future__ import annotations

import asyncio

import pytest

from baselines.pair_agent import PairAgent
from re_harness import Problem
from re_harness.budget import BudgetExceeded
from re_harness.lean import LeanRuntimeError
from re_harness.models import MODEL_A, MODEL_B

PROBLEM = Problem(
    id="p",
    description="prove True",
    challenge="import Mathlib\n\ntheorem p : True := by\n  sorry\n",
)
GOOD = "```lean\nimport Mathlib\n\ntheorem p : True := by\n  trivial\n```"
BAD = "```lean\nimport Mathlib\n\ntheorem p : True := by\n  exact 0\n```"


class FakeResponse:
    def __init__(self, content: str):
        self.content = content


class FakeLLM:
    """Per-model response queues; a response may be (delay_s, text)."""

    def __init__(self, responses: dict[str, list]):
        self.responses = {model: list(items) for model, items in responses.items()}
        self.requests: list[dict] = []

    async def complete(self, **kwargs):
        self.requests.append(kwargs)
        queue = self.responses[kwargs["model"]]
        item = queue.pop(0)
        if isinstance(item, tuple):
            delay, item = item
            await asyncio.sleep(delay)
        if isinstance(item, BaseException):
            raise item
        return FakeResponse(item)


class FakeCheck:
    def __init__(self, accepted: bool, messages=None, timed_out: bool = False):
        self.accepted = accepted
        self.messages = messages or []
        self.timed_out = timed_out


class FakeLean:
    """Accept exactly the sources containing `trivial`."""

    def __init__(self, error_messages=None):
        self.sources: list[str] = []
        self.error_messages = error_messages or [{"severity": "error", "data": "bad"}]

    async def check_file(self, source: str):
        self.sources.append(source)
        if "trivial" in source:
            return FakeCheck(True)
        return FakeCheck(False, list(self.error_messages))


class FakeServices:
    def __init__(self, llm, lean):
        self.llm = llm
        self.lean = lean
        self.checkpoints = []

    def checkpoint(self, source, metadata=None):
        self.checkpoints.append((source, metadata or {}))


def make_agent(**kwargs) -> PairAgent:
    kwargs.setdefault("max_turns", 3)
    kwargs.setdefault("time_limit_s", 1800)
    kwargs.setdefault("verify_reserve_s", 120)
    kwargs.setdefault("turn_guard_s", 0)
    kwargs.setdefault("restarts", False)
    return PairAgent(**kwargs)


@pytest.mark.asyncio
async def test_first_accepted_loop_wins_and_the_other_stops():
    # qwen's turns take 10 ms each; gpt-oss's first call is still in flight
    # (50 ms) when qwen's second candidate is accepted.
    llm = FakeLLM({MODEL_A: [(0.01, BAD), (0.01, GOOD), GOOD], MODEL_B: [(0.05, BAD), BAD, BAD]})
    services = FakeServices(llm, FakeLean())
    result = await make_agent().solve(PROBLEM, services)

    assert result.metadata["accepted_by_repl"] is True
    assert result.metadata["winner"] == MODEL_A
    assert "trivial" in result.solution
    loops = result.metadata["loops"]
    assert loops[MODEL_A]["stopped"] == "accepted"
    # gpt-oss had a call in flight when qwen won: it finished that call and
    # then stopped without checking or checkpointing over the winner.
    assert loops[MODEL_B]["stopped"] == "stop"
    assert loops[MODEL_B]["turns"] == 1
    assert all("trivial" in src or "exact 0" in src for src in services.lean.sources)
    assert services.checkpoints[-1][0] == result.solution
    models_called = {req["model"] for req in llm.requests}
    assert models_called == {MODEL_A, MODEL_B}


@pytest.mark.asyncio
async def test_prompts_match_the_raw_baseline_and_carry_feedback():
    llm = FakeLLM({MODEL_A: [BAD, BAD, BAD], MODEL_B: [BAD, BAD, BAD]})
    services = FakeServices(llm, FakeLean([{"severity": "error", "data": "type mismatch"}]))
    result = await make_agent().solve(PROBLEM, services)

    assert result.metadata["accepted_by_repl"] is False
    assert result.metadata["winner"] is None
    second_turns = [r for r in llm.requests if "Baseline turn: 2/3" in r["messages"][1]["content"]]
    assert len(second_turns) == 2
    assert all("type mismatch" in r["messages"][1]["content"] for r in second_turns)
    finals = [r for r in llm.requests if "final attempt" in r["messages"][0]["content"].lower()]
    assert len(finals) == 2
    assert all(loop["stopped"] == "turns" and loop["turns"] == 3
               for loop in result.metadata["loops"].values())


@pytest.mark.asyncio
async def test_budget_error_in_one_loop_does_not_stop_the_other():
    llm = FakeLLM({MODEL_A: [BudgetExceeded("no money")], MODEL_B: [BAD, GOOD, GOOD]})
    services = FakeServices(llm, FakeLean())
    result = await make_agent().solve(PROBLEM, services)

    assert result.metadata["winner"] == MODEL_B
    assert result.metadata["loops"][MODEL_A]["stopped"] == "error:BudgetExceeded"
    assert result.metadata["loops"][MODEL_B]["turns"] == 2


@pytest.mark.asyncio
async def test_fallback_picks_the_candidate_with_fewest_errors():
    class CountingLean(FakeLean):
        async def check_file(self, source):
            self.sources.append(source)
            errors = 1 if "exact 0" in source else 3
            return FakeCheck(False, [{"severity": "error", "data": "e"}] * errors)

    other = "```lean\nimport Mathlib\n\ntheorem p : True := by\n  omega\n```"
    llm = FakeLLM({MODEL_A: [other], MODEL_B: [BAD]})
    services = FakeServices(llm, CountingLean())
    result = await make_agent(max_turns=1).solve(PROBLEM, services)

    assert result.metadata["accepted_by_repl"] is False
    assert "exact 0" in result.solution
    assert result.metadata["origin"] == f"pair:{MODEL_B}"


@pytest.mark.asyncio
async def test_restarts_reopen_the_loop_until_the_window_closes():
    clock = {"t": 0.0}

    def fake_clock():
        clock["t"] += 100.0  # every clock read advances 100 s
        return clock["t"]

    llm = FakeLLM({MODEL_A: [BAD] * 20, MODEL_B: [BAD] * 20})
    services = FakeServices(llm, FakeLean())
    agent = make_agent(max_turns=2, restarts=True, time_limit_s=1000,
                       verify_reserve_s=100, turn_guard_s=300, clock=fake_clock)
    result = await agent.solve(PROBLEM, services)

    loops = result.metadata["loops"]
    assert result.metadata["arm"] == "pair+restarts"
    assert all(loop["stopped"] == "deadline" for loop in loops.values())
    assert any(loop["restarts"] >= 1 for loop in loops.values())
    # With restarts on, no turn is announced as the final attempt.
    assert not any("final attempt" in r["messages"][0]["content"].lower() for r in llm.requests)


@pytest.mark.asyncio
async def test_turn_guard_refuses_to_start_a_call_near_the_deadline():
    llm = FakeLLM({MODEL_A: [GOOD], MODEL_B: [GOOD]})
    services = FakeServices(llm, FakeLean())
    agent = make_agent(time_limit_s=400, verify_reserve_s=100, turn_guard_s=1000)
    result = await agent.solve(PROBLEM, services)

    assert llm.requests == []
    assert result.solution == PROBLEM.challenge
    assert all(loop["stopped"] == "deadline" for loop in result.metadata["loops"].values())


@pytest.mark.asyncio
async def test_repl_failure_is_retried_once_then_ends_the_loop():
    class FlakyLean(FakeLean):
        def __init__(self, failures: int):
            super().__init__()
            self.failures = failures

        async def check_file(self, source):
            if self.failures:
                self.failures -= 1
                raise LeanRuntimeError("REPL failed to import Mathlib: TIMEOUT after 180s")
            return await super().check_file(source)

    # One failure: the loop feeds back the outage and carries on to a solve.
    llm = FakeLLM({MODEL_A: [BAD, GOOD, GOOD], MODEL_B: [BudgetExceeded("skip")]})
    services = FakeServices(llm, FlakyLean(failures=1))
    result = await make_agent().solve(PROBLEM, services)
    assert result.metadata["winner"] == MODEL_A
    assert "unavailable" in llm.requests[1]["messages"][1]["content"]
    loop = result.metadata["loops"][MODEL_A]
    assert loop["turns"] == 2 and loop["attempts"][0]["timed_out"] is True

    # Two in a row: the loop stops and reports the REPL error.
    llm = FakeLLM({MODEL_A: [BAD, BAD, GOOD], MODEL_B: [BudgetExceeded("skip")]})
    services = FakeServices(llm, FlakyLean(failures=2))
    result = await make_agent().solve(PROBLEM, services)
    assert result.metadata["accepted_by_repl"] is False
    assert result.metadata["loops"][MODEL_A]["stopped"].startswith("error:LeanRuntimeError")
    assert result.metadata["loops"][MODEL_A]["turns"] == 2


@pytest.mark.asyncio
async def test_transient_call_errors_are_retried_then_fatal():
    from re_harness.llm import LLMCallError

    # Two faults, then a good reply: the loop retries the same turn and wins.
    llm = FakeLLM({MODEL_A: [LLMCallError("502"), LLMCallError("502"), GOOD],
                   MODEL_B: [BudgetExceeded("skip")]})
    services = FakeServices(llm, FakeLean())
    agent = make_agent(retry_pause_s=0)
    result = await agent.solve(PROBLEM, services)
    assert result.metadata["winner"] == MODEL_A
    assert result.metadata["loops"][MODEL_A]["turns"] == 1
    assert sum(1 for r in llm.requests if r["model"] == MODEL_A) == 3
    assert all("Baseline turn: 1/3" in r["messages"][1]["content"]
               for r in llm.requests if r["model"] == MODEL_A)

    # Three faults in a row end the loop.
    llm = FakeLLM({MODEL_A: [LLMCallError("x")] * 3, MODEL_B: [BudgetExceeded("skip")]})
    services = FakeServices(llm, FakeLean())
    result = await make_agent(retry_pause_s=0).solve(PROBLEM, services)
    assert result.metadata["loops"][MODEL_A]["stopped"].startswith("error:LLMCallError")


def test_guard_violation_detects_dropped_headers_and_extra_imports():
    from baselines.pair_agent import guard_violation

    challenge = "import Mathlib\n\ntheorem p : True := by\n  sorry\n"
    assert guard_violation(challenge, "import Mathlib\n\ntheorem p : True := by\n  trivial\n") is None
    assert "header" in guard_violation(challenge, "import Mathlib\n\nlemma helper : True := trivial\n")
    assert "header" in guard_violation(challenge, "import Mathlib\n\ntheorem p : 1 = 1 := by rfl\n")
    assert "import" in guard_violation(
        challenge, "import Mathlib\nimport Mathlib.NumberTheory.ArithmeticFunction\n\ntheorem p : True := by\n  trivial\n")


@pytest.mark.asyncio
async def test_guarded_loop_rejects_fragments_instead_of_accepting_them():
    fragment = "```lean\nimport Mathlib\n\nlemma helper : True := by\n  trivial\n```"
    llm = FakeLLM({MODEL_A: [fragment, GOOD, GOOD], MODEL_B: [BudgetExceeded("skip")]})
    services = FakeServices(llm, FakeLean())
    result = await make_agent(guard=True).solve(PROBLEM, services)
    assert result.metadata["winner"] == MODEL_A
    assert result.metadata["arm"] == "pair+guard"
    assert "header changed or missing" in llm.requests[1]["messages"][1]["content"]
    # The fragment was never checked or checkpointed.
    assert all("helper" not in src for src in services.lean.sources)
    assert all("helper" not in src for src, _ in services.checkpoints)

    # Without the guard the same fragment "wins", as the kit baseline would.
    llm = FakeLLM({MODEL_A: [fragment, GOOD], MODEL_B: [BudgetExceeded("skip")]})
    services = FakeServices(llm, FakeLean())
    result = await make_agent(guard=False).solve(PROBLEM, services)
    assert "helper" in result.solution and result.metadata["accepted_by_repl"] is True
