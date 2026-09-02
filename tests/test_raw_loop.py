"""Offline tests for research branch R1 (SUBMISSION_RAW_LOOP).

The stage runs the kit baseline's Qwen loop inside the controller. The
prompt and feedback format must match the baseline byte for byte, the
statement guard must still apply, and an accepted candidate must return as
the winner with the chain stopping there.
"""

from __future__ import annotations

from baselines.simple_agent import SimpleBaselineAgent, _format_messages
from re_harness import Problem, Services
from submission.agent import (
    QWEN,
    Candidate,
    Config,
    SubmissionAgent,
    Toolbox,
    raw_loop_feedback,
    raw_loop_messages,
)

CHALLENGE = "import Mathlib\n\ntheorem t : 1 + 1 = 2 := by sorry\n"
PROBLEM = Problem(id="t", description="Show 1 + 1 = 2.", challenge=CHALLENGE)
GOOD = "```lean\nimport Mathlib\n\ntheorem t : 1 + 1 = 2 := by\n  norm_num\n```"
BAD = "```lean\nimport Mathlib\n\ntheorem t : 1 + 1 = 2 := by\n  exact rfl\n```"
TAMPERED = "```lean\nimport Mathlib\n\ntheorem t : 1 + 1 = 3 := by\n  sorry\n```"


def make_config(**overrides):
    base = dict(time_limit_s=28800.0, verify_reserve_s=120.0, models="duo",
                disable_llm=False, qwen_samples=2, gptoss_samples=0,
                repair_rounds=0, sketch_rounds=0, gptoss_call_cap=0)
    base.update(overrides)
    return Config(**base)


def make_toolbox(config):
    services = Services(llm=None, lean=None, checkpoint=lambda s, m: None)
    tb = Toolbox(PROBLEM, services, config)
    tb.cycle = 1
    return tb


def stub(tb, replies, checks):
    """tb.sample returns replies in order; tb.check applies `checks` by source."""
    calls: list = []
    replies = list(replies)

    async def fake_sample(model, messages, *, kind, temperature=None, max_tokens=None):
        calls.append((model, kind, messages))
        return replies.pop(0) if replies else None

    async def fake_check(candidate, timeout_s=90):
        accepted, errors = checks(candidate.source)
        candidate.accepted = accepted
        candidate.error_count = 0 if accepted else len(errors)
        candidate.messages = errors
        return candidate

    tb.sample = fake_sample
    tb.check = fake_check
    return calls


def norm_num_accepts(source):
    if "norm_num" in source:
        return True, []
    return False, [{"severity": "error", "pos": {"line": 4, "column": 2},
                    "data": "type mismatch"},
                   {"severity": "warning", "pos": None, "data": "unused"}]


# ---- Config --------------------------------------------------------------


def test_config_raw_loop_default_off(monkeypatch):
    monkeypatch.delenv("SUBMISSION_RAW_LOOP", raising=False)
    monkeypatch.delenv("SUBMISSION_RAW_LOOP_TURNS", raising=False)
    cfg = Config.from_env()
    assert cfg.raw_loop is False and cfg.raw_loop_turns == 8


def test_config_raw_loop_env_on(monkeypatch):
    monkeypatch.setenv("SUBMISSION_RAW_LOOP", "1")
    monkeypatch.setenv("SUBMISSION_RAW_LOOP_TURNS", "5")
    cfg = Config.from_env()
    assert cfg.raw_loop is True and cfg.raw_loop_turns == 5


# ---- prompt and feedback parity with the kit baseline --------------------


def test_prompt_is_byte_identical_to_the_baseline():
    baseline = SimpleBaselineAgent(model=QWEN, max_turns=8)
    for turn, feedback in [(1, ""), (3, "error at None: boom"), (8, "x")]:
        ours = raw_loop_messages(PROBLEM, CHALLENGE, feedback=feedback, turn=turn, max_turns=8)
        theirs = baseline._messages(PROBLEM, feedback=feedback, turn=turn, is_last=(turn == 8))
        assert ours == theirs


def test_feedback_format_matches_the_baseline():
    messages = [{"severity": "error", "pos": {"line": 1, "column": 0}, "data": "bad "},
                {"severity": "warning", "pos": None, "data": "meh"},
                {"severity": "info", "data": "note"}]
    assert raw_loop_feedback(messages) == _format_messages(messages)


# ---- stage behaviour -----------------------------------------------------


async def test_stage_chains_feedback_and_returns_first_accepted():
    tb = make_toolbox(make_config(raw_loop=True, raw_loop_turns=4))
    calls = stub(tb, [BAD, GOOD, GOOD], norm_num_accepts)
    solved = await SubmissionAgent(tb.config).stage1r_rawloop(tb)

    assert solved is not None and solved.accepted
    assert solved.origin == "qwen-raw:s1r:t2"
    assert [kind for _, kind, _ in calls] == ["qwen-raw", "qwen-raw"]
    assert "Baseline turn: 1/4" in calls[0][2][1]["content"]
    second = calls[1][2][1]["content"]
    assert "Baseline turn: 2/4" in second
    assert "error at {'line': 4, 'column': 2}: type mismatch" in second
    assert "warning at None: unused" in second
    assert tb.best.origin == "qwen-raw:s1r:t2"
    assert any(e.get("stage") == "S1r" and e.get("accepted") for e in tb.stage_log)


async def test_stage_guards_tampered_statements_and_gives_up_after_turns():
    tb = make_toolbox(make_config(raw_loop=True, raw_loop_turns=3))
    calls = stub(tb, [TAMPERED, BAD, BAD], norm_num_accepts)
    solved = await SubmissionAgent(tb.config).stage1r_rawloop(tb)

    assert solved is None
    assert len(calls) == 3
    assert "keep them exactly as in the challenge" in calls[1][2][1]["content"]
    assert "final attempt" in calls[2][2][0]["content"].lower()
    assert tb.best.origin != "challenge"  # the near-miss was recorded as best-so-far


async def test_stage_skips_when_qwen_is_not_in_the_arm():
    tb = make_toolbox(make_config(raw_loop=True, models="gptoss"))
    calls = stub(tb, [GOOD], norm_num_accepts)
    assert await SubmissionAgent(tb.config).stage1r_rawloop(tb) is None
    assert calls == []


async def test_stage_stops_at_the_deadline():
    tb = make_toolbox(make_config(raw_loop=True, raw_loop_turns=3))
    calls = stub(tb, [GOOD], norm_num_accepts)
    tb.deadline.soft = tb.deadline.started  # no time left
    assert await SubmissionAgent(tb.config).stage1r_rawloop(tb) is None
    assert calls == []
    assert tb.stage_log[-1] == {"stage": "S1r", "turn": 1, "stopped": "deadline"}


async def test_stage_yields_after_its_share_of_the_window():
    tb = make_toolbox(make_config(raw_loop=True, raw_loop_turns=5, raw_loop_share=0.0))
    calls = stub(tb, [BAD, BAD, BAD], norm_num_accepts)
    assert await SubmissionAgent(tb.config).stage1r_rawloop(tb) is None
    assert len(calls) == 1  # one turn always runs; the share then stops it
    assert tb.stage_log[-1] == {"stage": "S1r", "turn": 2, "stopped": "share"}


def test_config_raw_loop_share_env(monkeypatch):
    monkeypatch.setenv("SUBMISSION_RAW_LOOP_SHARE", "0.3")
    assert Config.from_env().raw_loop_share == 0.3
    monkeypatch.delenv("SUBMISSION_RAW_LOOP_SHARE")
    assert Config.from_env().raw_loop_share == 0.45
