"""Offline tests for SUBMISSION_PREMISE_HINTS (B5): verified Mathlib names.

No Docker, no network — the LLM and REPL are trivial fakes.
"""

import time
from types import SimpleNamespace

import pytest

from re_harness import Problem, Services
from submission.agent import (
    Config,
    Toolbox,
    failed_premise_indexes,
    fill_messages,
    parse_premise_names,
)

CHALLENGE = """import Mathlib

theorem main : 1 + 1 = 2 := by sorry
"""


# ---- parser ----------------------------------------------------------------


def test_parse_premise_names_qualified_only():
    text = (
        "Nat.pow_mod\n"
        "- `Finset.sum_range_succ`\n"
        "3. ZMod.pow_card'\n"
        "omega\n"          # unqualified: never verifiable by name lists
        "just prose here\n"
    )
    assert parse_premise_names(text) == [
        "Nat.pow_mod", "Finset.sum_range_succ", "ZMod.pow_card'"]


def test_parse_premise_names_skips_prose_dotted_abbreviations():
    text = "use omega, e.g. Nat.succ_le_iff, i.e. the usual one"
    assert parse_premise_names(text) == ["Nat.succ_le_iff"]


def test_parse_premise_names_dedupes_and_caps():
    text = "\n".join(["Nat.pow_mod"] * 3 + [f"Foo.bar_{i}" for i in range(30)])
    names = parse_premise_names(text)
    assert names[0] == "Nat.pow_mod"
    assert len(names) == 15 == len(set(names))
    assert parse_premise_names(text, cap=4) == [
        "Nat.pow_mod", "Foo.bar_0", "Foo.bar_1", "Foo.bar_2"]


def test_parse_premise_names_empty_input():
    assert parse_premise_names("") == []
    assert parse_premise_names("no qualified names at all") == []


# ---- error-line-to-candidate mapping ---------------------------------------


def _msg(severity, line=None, data="x"):
    message = {"severity": severity, "data": data}
    if line is not None:
        message["pos"] = {"line": line, "column": 0}
    return message


def test_failed_indexes_maps_error_lines_to_candidates():
    messages = [
        _msg("info", 1, "Nat.pow_mod : ..."),          # #check success output
        _msg("error", 2, "unknown identifier 'Foo.bar'"),
        _msg("warning", 3, "deprecated"),               # exists: keep it
    ]
    assert failed_premise_indexes(messages, 3) == {1}


def test_failed_indexes_no_errors_keeps_everything():
    assert failed_premise_indexes([_msg("info", 1), _msg("info", 2)], 2) == set()
    assert failed_premise_indexes([], 3) == set()


def test_failed_indexes_unattributable_error_fails_all():
    # No position at all.
    assert failed_premise_indexes([_msg("error")], 3) == {0, 1, 2}
    # Line outside the candidate range (imports are stripped by the REPL,
    # so candidate k lives on kept line k+1 — line 9 maps to nothing).
    assert failed_premise_indexes([_msg("error", 9)], 3) == {0, 1, 2}


def test_failed_indexes_multiple_errors_one_line():
    messages = [_msg("error", 1), _msg("error", 1), _msg("error", 3)]
    assert failed_premise_indexes(messages, 3) == {0, 2}


# ---- Config flag -----------------------------------------------------------


def test_config_flag_default_off(monkeypatch):
    monkeypatch.delenv("SUBMISSION_PREMISE_HINTS", raising=False)
    assert not Config.from_env().premise_hints
    monkeypatch.setenv("SUBMISSION_PREMISE_HINTS", "1")
    assert Config.from_env().premise_hints
    monkeypatch.setenv("SUBMISSION_PREMISE_HINTS", "0")
    assert not Config.from_env().premise_hints


# ---- fill_messages injection -----------------------------------------------


def test_fill_messages_identical_when_hints_empty():
    problem = Problem(id="t", description="d", challenge=CHALLENGE)
    assert fill_messages(problem, "sketch", "main") == \
        fill_messages(problem, "sketch", "main", hints="")


def test_fill_messages_appends_hints_before_feedback():
    problem = Problem(id="t", description="d", challenge=CHALLENGE)
    hints = ("Verified available lemmas (these names exist; prefer them):\n"
             "- Nat.pow_mod")
    messages = fill_messages(problem, "sketch", "main", "some feedback", hints)
    user = messages[1]["content"]
    assert hints in user
    assert user.index(hints) < user.index("some feedback")
    assert hints not in fill_messages(problem, "sketch", "main", "some feedback")[1]["content"]


# ---- Toolbox.premise_hints (fakes; offline) --------------------------------


class FakeLLM:
    def __init__(self, content):
        self.content = content
        self.calls = 0
        self.kwargs = None

    async def complete(self, **kwargs):
        self.calls += 1
        self.kwargs = kwargs
        return SimpleNamespace(content=self.content, finish_reason="stop")


class BoomLLM:
    def __init__(self):
        self.calls = 0

    async def complete(self, **kwargs):
        self.calls += 1
        raise RuntimeError("boom")


class FakeLean:
    def __init__(self, messages):
        self.messages = messages
        self.sources = []

    async def check_file(self, source, *, timeout_s=None):
        self.sources.append(source)
        return SimpleNamespace(messages=self.messages, timed_out=False,
                               has_sorry=False, accepted=False)


def make_toolbox(tmp_path, llm, lean):
    problem = Problem(id="t", description="d", challenge=CHALLENGE)
    services = Services(
        llm=llm, lean=lean, checkpoint=lambda s, m: None, state_dir=tmp_path)
    return Toolbox(problem, services, Config.from_env())


@pytest.fixture(autouse=True)
def _clean_env(monkeypatch):
    for name in ("SUBMISSION_PREMISE_HINTS", "SUBMISSION_DISABLE_LLM",
                 "SUBMISSION_MODELS", "VM_TIME_LIMIT_S"):
        monkeypatch.delenv(name, raising=False)


async def test_premise_hints_end_to_end_and_cached(tmp_path):
    llm = FakeLLM("Nat.pow_mod\nFoo.bogus_name\nFinset.sum_range_succ\n")
    lean = FakeLean([  # kept line 2 = second #check = Foo.bogus_name
        _msg("error", 2, "unknown identifier 'Foo.bogus_name'"),
    ])
    tb = make_toolbox(tmp_path, llm, lean)
    hints = await tb.premise_hints()
    assert hints == ("Verified available lemmas (these names exist; "
                     "prefer them):\n- Nat.pow_mod\n- Finset.sum_range_succ")
    # The probe file: challenge imports, then one #check per line, nothing else.
    assert lean.sources[-1] == ("import Mathlib\n"
                                "#check Nat.pow_mod\n"
                                "#check Foo.bogus_name\n"
                                "#check Finset.sum_range_succ\n")
    assert llm.kwargs["max_tokens"] == 1000  # small, not the 16k sampling cap
    # Cached: a second call re-consults neither the LLM nor the REPL.
    assert await tb.premise_hints() == hints
    assert llm.calls == 1 and len(lean.sources) == 1


async def test_premise_hints_no_survivors_gives_empty(tmp_path):
    llm = FakeLLM("Foo.bogus\nBar.also_bogus\n")
    lean = FakeLean([_msg("error", 1), _msg("error", 2)])
    tb = make_toolbox(tmp_path, llm, lean)
    assert await tb.premise_hints() == ""
    assert await tb.premise_hints() == ""  # cached
    assert llm.calls == 1


async def test_premise_hints_swallows_failures_and_caches_empty(tmp_path):
    llm = BoomLLM()
    tb = make_toolbox(tmp_path, llm, FakeLean([]))
    assert await tb.premise_hints() == ""
    assert await tb.premise_hints() == ""
    assert llm.calls == 1  # the failure is cached too
    assert any(entry.get("stage") == "S4-premises" and "error" in entry
               for entry in tb.stage_log)


async def test_premise_hints_respects_deadline_and_llm_state(tmp_path):
    llm = FakeLLM("Nat.pow_mod\n")
    tb = make_toolbox(tmp_path, llm, FakeLean([]))
    tb.deadline.soft = time.monotonic() + 100  # < 240 s left: skip entirely
    assert await tb.premise_hints() == ""
    assert llm.calls == 0

    llm2 = FakeLLM("Nat.pow_mod\n")
    tb2 = make_toolbox(tmp_path, llm2, FakeLean([]))
    tb2.llm_alive = False
    assert await tb2.premise_hints() == ""
    assert llm2.calls == 0


async def test_premise_hints_skipped_in_gptoss_only_arm(tmp_path, monkeypatch):
    monkeypatch.setenv("SUBMISSION_MODELS", "gptoss")
    llm = FakeLLM("Nat.pow_mod\n")
    tb = make_toolbox(tmp_path, llm, FakeLean([]))
    assert await tb.premise_hints() == ""  # qwen must not leak into the arm
    assert llm.calls == 0
