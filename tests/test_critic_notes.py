"""Offline tests for research branch B8 (SUBMISSION_CRITIC_NOTES).

Covers the Config flag wiring, the bounded diagnosis prompt, and the
flag-guarded end-of-S2 critic: after a repair pass that closed nothing, at
most one gpt-oss diagnosis per problem, appended to tb.history_notes for
later S1 waves. No network; tb.sample is stubbed at stage level.
"""

from __future__ import annotations

import pytest

from re_harness import Problem, Services

from submission.agent import (
    GPTOSS,
    QWEN,
    Candidate,
    Config,
    LLMDead,
    SubmissionAgent,
    Toolbox,
    critic_messages,
)

CHALLENGE = "import Mathlib\n\ntheorem t : 1 + 1 = 2 := by sorry\n"

INSTRUCTION = ("In <=8 lines: diagnose the mathematical/technical root cause "
               "and state a concrete alternative approach. NO Lean code.")


# ---- Config flag ---------------------------------------------------------


def test_config_critic_notes_default_off(monkeypatch):
    monkeypatch.delenv("SUBMISSION_CRITIC_NOTES", raising=False)
    assert Config.from_env().critic_notes is False


def test_config_critic_notes_env_on(monkeypatch):
    monkeypatch.setenv("SUBMISSION_CRITIC_NOTES", "1")
    assert Config.from_env().critic_notes is True


def test_config_critic_notes_non_1_values_stay_off(monkeypatch):
    for raw in ("0", "", " ", "yes"):
        monkeypatch.setenv("SUBMISSION_CRITIC_NOTES", raw)
        assert Config.from_env().critic_notes is False


# ---- diagnosis prompt -----------------------------------------------------


def test_critic_messages_shape_truncation_and_instruction():
    problem = Problem(id="t", description="Show it.", challenge=CHALLENGE)
    messages = critic_messages(problem, "x" * 7000, "error at (3,30): nope")
    assert [m["role"] for m in messages] == ["system", "user"]
    user = messages[1]["content"]
    assert "x" * 6000 in user          # source included, truncated to 6000
    assert "x" * 6001 not in user
    assert "error at (3,30): nope" in user
    assert INSTRUCTION in user
    assert "NO Lean code" in messages[0]["content"]


# ---- stage2 wiring (offline, stubbed tb.sample) ---------------------------


def make_config(**overrides):
    base = dict(time_limit_s=28800.0, verify_reserve_s=120.0, models="duo",
                disable_llm=False, qwen_samples=2, gptoss_samples=2,
                repair_rounds=0, sketch_rounds=0, gptoss_call_cap=10)
    base.update(overrides)
    return Config(**base)


def make_toolbox(config):
    problem = Problem(id="t", description="Show it.", challenge=CHALLENGE)
    services = Services(llm=None, lean=None, checkpoint=lambda s, m: None)
    return Toolbox(problem, services, config)


def near_miss(errors=2, tactic="simp"):
    return Candidate(
        source=CHALLENGE.replace("sorry", tactic), origin="qwen-fast:s1",
        error_count=errors,
        messages=[{"severity": "error", "pos": {"line": 3, "column": 28},
                   "data": "unknown identifier 'foo'"}])


def record_sample(tb, calls, reply="Root cause: wrong lemma.\nTry induction."):
    async def fake_sample(model, messages, *, kind, temperature=None):
        calls.append((model, kind, messages))
        return reply

    tb.sample = fake_sample


async def test_flag_on_failed_repair_one_gptoss_call_and_note():
    config = make_config(critic_notes=True)
    tb = make_toolbox(config)
    calls: list = []
    record_sample(tb, calls)
    result = await SubmissionAgent(config).stage2_repair(tb, [near_miss()])
    assert result is None
    assert [(model, kind) for model, kind, _ in calls] == [(GPTOSS, "gptoss-med")]
    user = calls[0][2][1]["content"]
    assert "unknown identifier 'foo'" in user   # formatted errors included
    assert ":= by simp" in user                 # near-miss source included
    assert INSTRUCTION in user
    assert len(tb.history_notes) == 1
    note = tb.history_notes[0]
    assert note.startswith("gpt-oss diagnosis: ")
    assert "Root cause: wrong lemma." in note


async def test_note_truncated_to_800_chars():
    config = make_config(critic_notes=True)
    tb = make_toolbox(config)
    calls: list = []
    record_sample(tb, calls, reply="d" * 2000)
    await SubmissionAgent(config).stage2_repair(tb, [near_miss()])
    assert tb.history_notes == ["gpt-oss diagnosis: " + "d" * 800]


async def test_critic_diagnoses_best_near_miss():
    config = make_config(critic_notes=True)
    tb = make_toolbox(config)
    calls: list = []
    record_sample(tb, calls)
    worse = near_miss(errors=9, tactic="ring_nf")
    best = near_miss(errors=2, tactic="omega")
    await SubmissionAgent(config).stage2_repair(tb, [worse, best])
    user = calls[0][2][1]["content"]
    assert ":= by omega" in user
    assert "ring_nf" not in user


async def test_flag_off_zero_calls_and_history_unchanged():
    config = make_config()  # critic_notes defaults to False
    tb = make_toolbox(config)
    tb.history_notes.append("cycle 1, qwen-fast x3: best had 2 errors")
    before = list(tb.history_notes)
    calls: list = []
    record_sample(tb, calls)
    result = await SubmissionAgent(config).stage2_repair(tb, [near_miss()])
    assert result is None
    assert calls == []
    assert tb.history_notes == before


async def test_once_per_problem_across_two_invocations():
    config = make_config(critic_notes=True)
    tb = make_toolbox(config)
    calls: list = []
    record_sample(tb, calls)
    agent = SubmissionAgent(config)
    await agent.stage2_repair(tb, [near_miss()])
    await agent.stage2_repair(tb, [near_miss()])
    assert [(model, kind) for model, kind, _ in calls] == [(GPTOSS, "gptoss-med")]
    assert len(tb.history_notes) == 1


async def test_qwen_only_arm_never_calls():
    config = make_config(critic_notes=True, models="qwen")
    tb = make_toolbox(config)
    calls: list = []
    record_sample(tb, calls)
    assert await SubmissionAgent(config).stage2_repair(tb, [near_miss()]) is None
    assert calls == []
    assert tb.history_notes == []


async def test_no_near_misses_no_call():
    config = make_config(critic_notes=True)
    tb = make_toolbox(config)
    calls: list = []
    record_sample(tb, calls)
    assert await SubmissionAgent(config).stage2_repair(tb, []) is None
    assert calls == []
    assert tb.history_notes == []


async def test_deadline_starved_skips():
    config = make_config(critic_notes=True)
    tb = make_toolbox(config)
    tb.deadline.allows = lambda seconds: False  # type: ignore[method-assign]
    calls: list = []
    record_sample(tb, calls)
    assert await SubmissionAgent(config).stage2_repair(tb, [near_miss()]) is None
    assert calls == []
    assert tb.history_notes == []


async def test_call_failure_skips_silently_and_never_retries():
    config = make_config(critic_notes=True)
    tb = make_toolbox(config)
    calls: list = []
    record_sample(tb, calls, reply=None)  # provider hiccup: sample yields None
    agent = SubmissionAgent(config)
    assert await agent.stage2_repair(tb, [near_miss()]) is None
    assert tb.history_notes == []
    assert len(calls) == 1
    # The one slot is spent: a later failed repair pass does not try again.
    await agent.stage2_repair(tb, [near_miss()])
    assert len(calls) == 1


async def test_gptoss_call_cap_respected_via_real_sample():
    # Real Toolbox.sample: at the cap it returns None before touching the LLM.
    config = make_config(critic_notes=True, gptoss_call_cap=3)
    tb = make_toolbox(config)
    tb.gptoss_calls = 3  # cap already spent by earlier stages
    assert await SubmissionAgent(config).stage2_repair(tb, [near_miss()]) is None
    assert tb.history_notes == []
    assert tb.gptoss_calls == 3


async def test_llmdead_propagates():
    config = make_config(critic_notes=True)
    tb = make_toolbox(config)

    async def dead_sample(model, messages, *, kind, temperature=None):
        raise LLMDead

    tb.sample = dead_sample
    with pytest.raises(LLMDead):
        await SubmissionAgent(config).stage2_repair(tb, [near_miss()])


async def test_solved_repair_skips_critic():
    config = make_config(critic_notes=True, repair_rounds=1)
    tb = make_toolbox(config)
    calls: list = []

    async def fake_sample(model, messages, *, kind, temperature=None):
        calls.append((model, kind))
        return "```lean\n" + CHALLENGE.replace("sorry", "norm_num") + "```"

    async def fake_check(candidate, timeout_s=90):
        candidate.accepted = True
        candidate.error_count = 0
        return candidate

    tb.sample = fake_sample
    tb.check = fake_check
    result = await SubmissionAgent(config).stage2_repair(tb, [near_miss()])
    assert result is not None and result.accepted
    assert calls == [(QWEN, "qwen-think")]  # the repair round only, no critic
    assert tb.history_notes == []
