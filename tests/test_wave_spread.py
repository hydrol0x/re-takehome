"""Offline tests for SUBMISSION_WAVE_SPREAD (research branch B1).

Mirrors tests/test_agent_state.py: real Config/Toolbox objects, no network;
LLM and lean services stubbed out.
"""

from types import SimpleNamespace

from re_harness import Problem, Services
from submission.agent import (
    QWEN,
    WAVE_SPREAD_TEMPS,
    Config,
    SubmissionAgent,
    Toolbox,
    wave_spread_temperature,
)

CHALLENGE = """import Mathlib

theorem main : 1 + 1 = 2 := by sorry
"""


def clear_env(monkeypatch):
    for name in ("SUBMISSION_WAVE_SPREAD", "SUBMISSION_MODELS",
                 "SUBMISSION_QWEN_SAMPLES", "SUBMISSION_GPTOSS_SAMPLES",
                 "SUBMISSION_SHORTCAP", "SUBMISSION_DISABLE_LLM",
                 "VM_TIME_LIMIT_S", "VM_VERIFY_RESERVE_S"):
        monkeypatch.delenv(name, raising=False)


# ---- Config flag plumbing --------------------------------------------------


def test_flag_off_by_default(monkeypatch):
    clear_env(monkeypatch)
    assert Config.from_env().wave_spread is False


def test_flag_on(monkeypatch):
    clear_env(monkeypatch)
    monkeypatch.setenv("SUBMISSION_WAVE_SPREAD", "1")
    assert Config.from_env().wave_spread is True


def test_flag_non_1_values_stay_off(monkeypatch):
    clear_env(monkeypatch)
    for raw in ("0", "", " ", "yes"):
        monkeypatch.setenv("SUBMISSION_WAVE_SPREAD", raw)
        assert Config.from_env().wave_spread is False


# ---- Pure temperature-cycle helper -----------------------------------------


def test_temperature_cycle_values_and_period():
    assert WAVE_SPREAD_TEMPS == (0.5, 0.8, 1.1)
    assert [wave_spread_temperature(i) for i in range(7)] == [
        0.5, 0.8, 1.1, 0.5, 0.8, 1.1, 0.5]
    assert wave_spread_temperature(3 * 10**6 + 2) == 1.1


# ---- S1 wave behavior (stage1_sample with a recording sample stub) ---------


def make_agent_and_toolbox(tmp_path):
    config = Config.from_env()
    problem = Problem(id="t", description="d", challenge=CHALLENGE)
    services = Services(
        llm=None, lean=None, checkpoint=lambda s, m: None, state_dir=tmp_path
    )
    return SubmissionAgent(config), Toolbox(problem, services, config)


async def run_stage1(monkeypatch, tmp_path):
    """Run one S1 wave, recording (kind, temperature) of every sample call."""

    agent, tb = make_agent_and_toolbox(tmp_path)
    calls: list[tuple[str, float | None]] = []

    async def fake_sample(model, messages, *, kind, temperature=None):
        calls.append((kind, temperature))
        return None  # no usable candidates: wave runs to completion, no lean

    monkeypatch.setattr(tb, "sample", fake_sample)
    solved, near_misses = await agent.stage1_sample(tb)
    assert solved is None and near_misses == []
    return calls


async def test_flag_off_short_window_wave_unchanged(monkeypatch, tmp_path):
    clear_env(monkeypatch)
    monkeypatch.setenv("VM_TIME_LIMIT_S", "1200")  # agent window 1080 s < 2400
    calls = await run_stage1(monkeypatch, tmp_path)
    fast = [t for k, t in calls if k == "qwen-fast"]
    assert len(fast) == 8            # today's wave size, no growth
    assert fast == [None] * 8        # no overrides: profile t=0.8 applies
    assert [t for k, t in calls if k == "qwen-think"] == [None]


async def test_flag_on_short_window_grows_and_spreads(monkeypatch, tmp_path):
    clear_env(monkeypatch)
    monkeypatch.setenv("VM_TIME_LIMIT_S", "1200")  # agent window 1080 s < 2400
    monkeypatch.setenv("SUBMISSION_WAVE_SPREAD", "1")
    calls = await run_stage1(monkeypatch, tmp_path)
    fast = [t for k, t in calls if k == "qwen-fast"]
    assert len(fast) == 10           # 8 default + 2 short-window growth
    assert fast == [wave_spread_temperature(i) for i in range(10)]
    # qwen-think keeps its own profile temperature (no override)
    assert [t for k, t in calls if k == "qwen-think"] == [None]


async def test_flag_on_long_window_spreads_without_growth(monkeypatch, tmp_path):
    clear_env(monkeypatch)  # default window 28800 s: agent_time_s >= 2400
    monkeypatch.setenv("SUBMISSION_WAVE_SPREAD", "1")
    calls = await run_stage1(monkeypatch, tmp_path)
    fast = [t for k, t in calls if k == "qwen-fast"]
    assert len(fast) == 8            # growth is short-window-only
    assert fast == [wave_spread_temperature(i) for i in range(8)]


# ---- sample() per-call temperature override --------------------------------


class RecordingLLM:
    def __init__(self):
        self.calls: list[dict] = []

    async def complete(self, **kwargs):
        self.calls.append(kwargs)
        return SimpleNamespace(finish_reason="stop", content="ok")


async def test_sample_temperature_override_reaches_llm(monkeypatch, tmp_path):
    clear_env(monkeypatch)
    llm = RecordingLLM()
    problem = Problem(id="t", description="d", challenge=CHALLENGE)
    services = Services(
        llm=llm, lean=None, checkpoint=lambda s, m: None, state_dir=tmp_path
    )
    tb = Toolbox(problem, services, Config.from_env())
    messages = [{"role": "user", "content": "x"}]
    assert await tb.sample(QWEN, messages, kind="qwen-fast") == "ok"
    assert await tb.sample(QWEN, messages, kind="qwen-fast", temperature=1.1) == "ok"
    assert llm.calls[0]["temperature"] == 0.8  # default call site: profile value
    assert llm.calls[1]["temperature"] == 1.1  # override wins over the profile
