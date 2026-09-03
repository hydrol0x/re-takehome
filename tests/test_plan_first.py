"""Offline tests for research branch B2 (SUBMISSION_PLAN_FIRST, DSP-lite).

Covers the pure plan-selection helper `pick_plan`, the Config flag wiring,
and the flag-guarded prompt conditioning in `whole_proof_messages`.
"""

from __future__ import annotations

import pytest

from re_harness import Problem, Services

from submission.agent import (
    QWEN,
    Config,
    LLMDead,
    SubmissionAgent,
    Toolbox,
    pick_plan,
    plan_messages,
    whole_proof_messages,
)


# ---- pick_plan: majority selection --------------------------------------


def test_pick_plan_majority_two_agree():
    a = "Use induction on n.\nThen close with omega."
    b = "Try a direct computation with decide."
    c = "Use induction on n.\nFinish by norm_num."
    assert pick_plan([a, b, c]) == a  # first plan of the agreeing pair


def test_pick_plan_majority_ignores_case_punctuation_and_spacing():
    a = "Use  Induction on n!!"
    b = "use induction, on n"
    c = "Pigeonhole over residues mod 7, then a finite check."
    assert pick_plan([c, a, b]) == a


def test_pick_plan_no_majority_picks_longest():
    a = "Induct on n."
    b = "Pigeonhole argument over residues, then finite case check with omega."
    c = "Direct decide."
    assert pick_plan([a, b, c]) == b


def test_pick_plan_single_plan_returned():
    assert pick_plan(["Only one idea."]) == "Only one idea."


def test_pick_plan_strips_surrounding_whitespace():
    assert pick_plan(["\n\n  Induct on n.  \n"]) == "Induct on n."


# ---- pick_plan: empty/None inputs ---------------------------------------


def test_pick_plan_empty_and_none_inputs():
    assert pick_plan([]) is None
    assert pick_plan(None) is None
    assert pick_plan(["", "   ", "\n\n"]) is None


def test_pick_plan_ignores_non_string_entries():
    assert pick_plan([None, 3, "Induct on n."]) == "Induct on n."  # type: ignore[list-item]
    assert pick_plan([None, None]) is None  # type: ignore[list-item]


# ---- Config flag ---------------------------------------------------------


def test_config_plan_first_default_off(monkeypatch):
    monkeypatch.delenv("SUBMISSION_PLAN_FIRST", raising=False)
    assert Config.from_env().plan_first is False


def test_config_plan_first_env_on(monkeypatch):
    monkeypatch.setenv("SUBMISSION_PLAN_FIRST", "1")
    assert Config.from_env().plan_first is True


def test_config_plan_first_only_literal_one_enables(monkeypatch):
    monkeypatch.setenv("SUBMISSION_PLAN_FIRST", "0")
    assert Config.from_env().plan_first is False
    monkeypatch.setenv("SUBMISSION_PLAN_FIRST", "yes")
    assert Config.from_env().plan_first is False


# ---- prompt conditioning -------------------------------------------------

PROBLEM = Problem(id="t", description="Show 1 + 1 = 2.", challenge="theorem t : 1 + 1 = 2 := by sorry\n")


def test_whole_proof_messages_without_plan_is_unchanged():
    default = whole_proof_messages(PROBLEM, PROBLEM.challenge)
    explicit = whole_proof_messages(PROBLEM, PROBLEM.challenge, plan="")
    assert default == explicit
    assert "A promising strategy:" not in explicit[1]["content"]


def test_whole_proof_messages_prepends_plan_block():
    messages = whole_proof_messages(PROBLEM, PROBLEM.challenge, plan="Induct on n.")
    user = messages[1]["content"]
    assert user.startswith(
        "A promising strategy:\nInduct on n.\nFollow it unless clearly wrong.\n")
    # The original prompt body still follows, untouched.
    assert whole_proof_messages(PROBLEM, PROBLEM.challenge)[1]["content"] in user
    assert messages[0] == whole_proof_messages(PROBLEM, PROBLEM.challenge)[0]


def test_plan_messages_shape():
    messages = plan_messages(PROBLEM, PROBLEM.challenge)
    assert [m["role"] for m in messages] == ["system", "user"]
    assert "no Lean code" in messages[1]["content"]
    assert PROBLEM.description in messages[1]["content"]


# ---- stage1 wiring (offline, stubbed tb.sample) --------------------------

PLAN_MARKER = "proof strategy; no Lean code"
PLANS = ["Use induction on n.\nDetails A.",
         "Try a direct decide.",
         "Use induction on n!\nDetails B."]


def make_config(**overrides):
    base = dict(time_limit_s=28800.0, verify_reserve_s=120.0, models="qwen",
                disable_llm=False, qwen_samples=2, gptoss_samples=0,
                repair_rounds=0, sketch_rounds=0, gptoss_call_cap=0)
    base.update(overrides)
    return Config(**base)


def make_toolbox(config, cycle):
    problem = Problem(
        id="t", description="Show it.",
        challenge="import Mathlib\n\ntheorem t : 1 + 1 = 2 := by sorry\n")
    services = Services(llm=None, lean=None, checkpoint=lambda s, m: None)
    tb = Toolbox(problem, services, config)
    tb.cycle = cycle
    return tb


def stub_sample(tb, calls):
    plans = iter(PLANS)

    async def fake_sample(model, messages, *, kind, temperature=None):
        calls.append((kind, messages))
        if PLAN_MARKER in messages[1]["content"]:
            return next(plans, None)
        return None  # wave samples yield nothing usable

    tb.sample = fake_sample


async def test_stage1_cycle1_flag_on_conditions_qwen_fast_only():
    config = make_config(plan_first=True)
    tb = make_toolbox(config, cycle=1)
    calls: list = []
    stub_sample(tb, calls)
    solved, near = await SubmissionAgent(config).stage1_sample(tb)
    assert solved is None and near == []
    plan_calls = [c for c in calls if PLAN_MARKER in c[1][1]["content"]]
    wave_calls = [c for c in calls if PLAN_MARKER not in c[1][1]["content"]]
    assert len(plan_calls) == 3
    assert all(kind == "qwen-fast" for kind, _ in plan_calls)
    assert [kind for kind, _ in wave_calls] == ["qwen-fast", "qwen-fast", "qwen-think"]
    for kind, messages in wave_calls:
        content = messages[1]["content"]
        if kind == "qwen-fast":  # majority plan (PLANS[0]) prepended
            assert content.startswith(
                "A promising strategy:\nUse induction on n.\nDetails A.\n"
                "Follow it unless clearly wrong.\n")
        else:  # qwen-think keeps the unconditioned prompt
            assert "A promising strategy:" not in content


async def test_stage1_flag_off_makes_no_plan_calls():
    config = make_config()  # plan_first defaults to False
    tb = make_toolbox(config, cycle=1)
    calls: list = []
    stub_sample(tb, calls)
    await SubmissionAgent(config).stage1_sample(tb)
    assert all(PLAN_MARKER not in messages[1]["content"] for _, messages in calls)
    assert all("A promising strategy:" not in messages[1]["content"]
               for _, messages in calls)
    assert len(calls) == 3  # the wave alone


async def test_stage1_cycle2_flag_on_skips_plan_step():
    config = make_config(plan_first=True)
    tb = make_toolbox(config, cycle=2)
    calls: list = []
    stub_sample(tb, calls)
    await SubmissionAgent(config).stage1_sample(tb)
    assert all(PLAN_MARKER not in messages[1]["content"] for _, messages in calls)
    assert all("A promising strategy:" not in messages[1]["content"]
               for _, messages in calls)


async def test_stage1_budget_starved_skips_plan_step():
    config = make_config(plan_first=True)
    tb = make_toolbox(config, cycle=1)
    tb.deadline.allows = lambda seconds: False  # type: ignore[method-assign]
    calls: list = []
    stub_sample(tb, calls)
    await SubmissionAgent(config).stage1_sample(tb)
    assert all(PLAN_MARKER not in messages[1]["content"] for _, messages in calls)


async def test_stage1_plan_step_propagates_llmdead():
    config = make_config(plan_first=True)
    tb = make_toolbox(config, cycle=1)

    async def dead_sample(model, messages, *, kind):
        raise LLMDead

    tb.sample = dead_sample
    with pytest.raises(LLMDead):
        await SubmissionAgent(config).stage1_sample(tb)
