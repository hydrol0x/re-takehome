"""Offline tests for the agent's durable per-problem state (resume support)."""

import asyncio
import json

from re_harness import LeanCheck, Problem, Services
from submission.agent import Config, SubmissionAgent, Toolbox

CHALLENGE = """import Mathlib

abbrev answer : ℕ := sorry

theorem main : answer = 6 := by sorry
"""


def make_toolbox(tmp_path, challenge=CHALLENGE):
    problem = Problem(id="t", description="d", challenge=challenge)
    services = Services(
        llm=None, lean=None, checkpoint=lambda s, m: None, state_dir=tmp_path
    )
    return Toolbox(problem, services, Config.from_env())


def test_state_roundtrip_restores_progress(tmp_path):
    tb = make_toolbox(tmp_path)
    assert not tb.s0_done and tb.cycles_done == 0 and not tb.pinned_answers
    tb.pin_answers({"answer": 6})
    tb.s0_done = True
    tb.cycles_done = 3
    tb.lemma_pool = "lemma helper : True := trivial"
    tb.history_notes = ["cycle 1: linarith failed"]
    tb.save_state()

    tb2 = make_toolbox(tmp_path)
    assert tb2.s0_done
    assert tb2.cycles_done == 3
    assert tb2.pinned_answers == {"answer": 6}
    assert ":= 6" in tb2.challenge and "answer" in tb2.challenge
    assert tb2.lemma_pool.startswith("lemma helper")
    assert tb2.history_notes == ["cycle 1: linarith failed"]


def test_state_ignored_for_different_challenge(tmp_path):
    tb = make_toolbox(tmp_path)
    tb.s0_done = True
    tb.save_state()
    tb2 = make_toolbox(tmp_path, challenge=CHALLENGE + "-- edited\n")
    assert not tb2.s0_done


def test_corrupt_state_is_ignored(tmp_path):
    (tmp_path / "agent_state.json").write_text("{not json")
    tb = make_toolbox(tmp_path)
    assert not tb.s0_done and tb.cycles_done == 0


def test_scaled_constants(monkeypatch):
    monkeypatch.setenv("VM_TIME_LIMIT_S", "1200")
    monkeypatch.setenv("SUBMISSION_SHORTCAP", "0")
    assert Config.from_env().scaled(960) == 960  # opted out: identity
    monkeypatch.delenv("SUBMISSION_SHORTCAP", raising=False)
    short = Config.from_env()  # promoted default: on
    assert short.shortcap
    assert short.scaled(960) == 960 * (short.agent_time_s / 2400)
    assert short.scaled(10) == 60  # floor
    monkeypatch.setenv("VM_TIME_LIMIT_S", "28800")
    assert Config.from_env().scaled(960) == 960  # long window: identity


SKELETON = "lemma helper : 1 + 1 = 2 := by sorry\n\n" + CHALLENGE


def test_kept_skeleton_roundtrip(tmp_path, monkeypatch):
    monkeypatch.setenv("SUBMISSION_SKELETON_KEEP", "1")
    tb = make_toolbox(tmp_path)
    assert tb.kept_skeleton == "" and tb.kept_skeleton_holes == 10**6
    tb.kept_skeleton = SKELETON
    tb.kept_skeleton_holes = 1
    tb.kept_skeleton_errors = 0
    tb.save_state()

    tb2 = make_toolbox(tmp_path)
    assert tb2.kept_skeleton == SKELETON
    assert tb2.kept_skeleton_holes == 1
    assert tb2.kept_skeleton_errors == 0


def test_kept_skeleton_ignored_when_flag_off(tmp_path, monkeypatch):
    monkeypatch.setenv("SUBMISSION_SKELETON_KEEP", "1")
    tb = make_toolbox(tmp_path)
    tb.kept_skeleton = SKELETON
    tb.kept_skeleton_holes = 1
    tb.kept_skeleton_errors = 0
    tb.save_state()

    monkeypatch.delenv("SUBMISSION_SKELETON_KEEP")
    tb2 = make_toolbox(tmp_path)
    assert tb2.kept_skeleton == "" and tb2.kept_skeleton_holes == 10**6
    tb2.save_state()  # flag off: the fields never reach the state file
    state = json.loads((tmp_path / "agent_state.json").read_text())
    assert "kept_skeleton" not in state


def test_kept_skeleton_oversized_is_dropped(tmp_path, monkeypatch):
    monkeypatch.setenv("SUBMISSION_SKELETON_KEEP", "1")
    tb = make_toolbox(tmp_path)
    tb.kept_skeleton = "-- comment\n" * 8000  # > 40000 chars
    tb.kept_skeleton_holes = 2
    tb.kept_skeleton_errors = 0
    tb.save_state()

    tb2 = make_toolbox(tmp_path)
    assert tb2.kept_skeleton == "" and tb2.kept_skeleton_holes == 10**6


def test_kept_skeleton_guarded_by_challenge_sha(tmp_path, monkeypatch):
    monkeypatch.setenv("SUBMISSION_SKELETON_KEEP", "1")
    tb = make_toolbox(tmp_path)
    tb.kept_skeleton = SKELETON
    tb.kept_skeleton_holes = 1
    tb.save_state()
    tb2 = make_toolbox(tmp_path, challenge=CHALLENGE + "-- edited\n")
    assert tb2.kept_skeleton == "" and tb2.kept_skeleton_holes == 10**6


def test_no_state_dir_is_inert(tmp_path):
    problem = Problem(id="t", description="d", challenge=CHALLENGE)
    services = Services(llm=None, lean=None, checkpoint=lambda s, m: None)
    tb = Toolbox(problem, services, Config.from_env())
    tb.save_state()  # must not raise
    assert tb.state_path is None


def test_bound_templates_flag(monkeypatch):
    monkeypatch.delenv("SUBMISSION_BOUND_TEMPLATES", raising=False)
    assert not Config.from_env().bound_templates  # default off
    monkeypatch.setenv("SUBMISSION_BOUND_TEMPLATES", "1")
    assert Config.from_env().bound_templates
    monkeypatch.setenv("SUBMISSION_BOUND_TEMPLATES", "0")
    assert not Config.from_env().bound_templates


BOUNDED = """import Mathlib

theorem bounded : ∀ n, n ≤ 12 → n * 0 = 0 := by
  sorry
"""


class _AcceptAllLean:
    """Fake REPL that accepts every file and records what was checked."""

    def __init__(self):
        self.sources = []

    async def check_file(self, source, *, timeout_s=None):
        self.sources.append(source)
        return LeanCheck(accepted=True, messages=[], has_sorry=False,
                         timed_out=False, duration_ms=1)


def _cascade(tmp_path):
    lean = _AcceptAllLean()
    problem = Problem(id="t", description="d", challenge=BOUNDED)
    services = Services(
        llm=None, lean=lean, checkpoint=lambda s, m: None, state_dir=tmp_path
    )
    tb = Toolbox(problem, services, Config.from_env())
    agent = SubmissionAgent(tb.config)
    filled = asyncio.run(agent._cascade_hole(tb, BOUNDED, 0, "bounded"))
    return filled, lean


def test_cascade_tries_bound_templates_first(tmp_path, monkeypatch):
    monkeypatch.setenv("SUBMISSION_BOUND_TEMPLATES", "1")
    filled, lean = _cascade(tmp_path)
    assert filled is not None
    assert "intro n hn" in filled and "interval_cases n <;> omega" in filled
    assert len(lean.sources) == 1  # template accepted before any FILL_SWEEP entry


def test_cascade_unchanged_when_flag_off(tmp_path, monkeypatch):
    monkeypatch.delenv("SUBMISSION_BOUND_TEMPLATES", raising=False)
    filled, lean = _cascade(tmp_path)
    assert filled is not None
    assert "linarith" in filled  # FILL_SWEEP[0], exactly as before
    assert "interval_cases" not in filled
    assert len(lean.sources) == 1
