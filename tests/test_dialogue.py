"""Offline tests for the dialogue mechanisms (research branches D1/D2)."""

from re_harness import Problem, Services

from submission.agent import (
    GPTOSS, QWEN, Candidate, Config, SubmissionAgent, Toolbox,
    critique_messages, plan_critique_messages,
)

CHALLENGE = "import Mathlib\n\ntheorem main : 1 + 1 = 2 := by sorry\n"


def make(**overrides):
    base = dict(time_limit_s=1800.0, verify_reserve_s=120.0, models="duo",
                disable_llm=False, qwen_samples=2, gptoss_samples=1, repair_rounds=2,
                sketch_rounds=1, gptoss_call_cap=4)
    base.update(overrides)
    config = Config(**base)
    problem = Problem(id="t", description="d", challenge=CHALLENGE)
    services = Services(llm=None, lean=None, checkpoint=lambda s, m: None)
    return SubmissionAgent(config), Toolbox(problem, services, config)


def test_flags_default_off_and_env_on(monkeypatch):
    monkeypatch.delenv("SUBMISSION_DIALOGUE_REPAIR", raising=False)
    monkeypatch.delenv("SUBMISSION_DIALOGUE_SKETCH", raising=False)
    c = Config.from_env()
    assert c.dialogue_repair is False and c.dialogue_sketch is False
    monkeypatch.setenv("SUBMISSION_DIALOGUE_REPAIR", "1")
    monkeypatch.setenv("SUBMISSION_DIALOGUE_SKETCH", "1")
    c = Config.from_env()
    assert c.dialogue_repair is True and c.dialogue_sketch is True


def test_prompts_are_reviews_not_proofs():
    problem = Problem(id="t", description="d", challenge=CHALLENGE)
    sys_, user = (m["content"] for m in critique_messages(problem, "theorem x := by omega", "error: omega failed"))
    assert "Do NOT write the full proof" in sys_ and "omega failed" in user
    sys2, user2 = (m["content"] for m in plan_critique_messages(problem, "induct on n"))
    assert "Do NOT write Lean code" in sys2 and "induct on n" in user2


async def test_dialogue_repair_calls_reviewer_then_author():
    agent, tb = make(dialogue_repair=True)
    calls = []

    async def fake_sample(model, messages, *, kind, temperature=None, max_tokens=None):
        calls.append((model, kind))
        if len(calls) == 1:                      # reviewer
            assert "reviewer" in messages[0]["content"]
            return "Use Nat.succ_le_iff at line 3."
        assert "Review from a second prover" in messages[1]["content"]
        return "```lean\ntheorem main : 1 + 1 = 2 := by\n  decide\n```"

    async def fake_check(candidate, timeout_s=90):
        candidate.accepted = True
        candidate.error_count = 0
        candidate.messages = []
        return candidate

    tb.sample = fake_sample
    tb.check = fake_check
    tb.record = lambda c, s: None
    failing = Candidate(source=CHALLENGE.replace("sorry", "omega"), origin="qwen-fast:s1",
                        accepted=False, error_count=1,
                        messages=[{"severity": "error", "data": "omega failed"}])
    result = await agent.repair_with_handoff(
        tb, failing, origin_model=QWEN,
        build_messages=lambda fb: [{"role": "system", "content": "s"},
                                   {"role": "user", "content": fb}],
        guard=lambda src: src, stage="S2")
    assert result is not None and result.accepted
    assert calls == [(GPTOSS, "gptoss-med"), (QWEN, "qwen-think")]


async def test_dialogue_repair_off_is_single_call():
    agent, tb = make(dialogue_repair=False)
    calls = []

    async def fake_sample(model, messages, *, kind, temperature=None, max_tokens=None):
        calls.append(model)
        return "```lean\ntheorem main : 1 + 1 = 2 := by\n  decide\n```"

    async def fake_check(candidate, timeout_s=90):
        candidate.accepted = True; candidate.error_count = 0; candidate.messages = []
        return candidate

    tb.sample = fake_sample; tb.check = fake_check; tb.record = lambda c, s: None
    failing = Candidate(source=CHALLENGE.replace("sorry", "omega"), origin="qwen-fast:s1",
                        accepted=False, error_count=1,
                        messages=[{"severity": "error", "data": "omega failed"}])
    await agent.repair_with_handoff(
        tb, failing, origin_model=QWEN,
        build_messages=lambda fb: [{"role": "system", "content": "s"}, {"role": "user", "content": fb}],
        guard=lambda src: src, stage="S2")
    assert calls == [QWEN]
