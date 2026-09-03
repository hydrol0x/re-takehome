"""Offline tests for research branch B7 (SUBMISSION_STRENGTHEN_IH).

Covers the pure `induction_like` predicate, the Config flag wiring, the
flag-guarded per-decl fill-failure bookkeeping in `_fill_one_hole`, and the
re-sketch note addendum `strengthen_ih_note` (unit + stage4 wiring).
"""

from __future__ import annotations

import asyncio

from re_harness import LeanCheck, Problem, Services

from submission.agent import (
    Config,
    LLMDead,
    SubmissionAgent,
    Toolbox,
    induction_like,
    strengthen_ih_note,
)

STRENGTHEN_MARKER = "the induction hypothesis as stated appears too weak"


# ---- induction_like: pure predicate --------------------------------------


def test_induction_like_forall_over_nat():
    assert induction_like("theorem h : ∀ n : ℕ, n + 0 = n :=")
    assert induction_like("lemma l : ∀ (m : ℕ), m ≤ m + 1 :=")
    assert induction_like("lemma l : ∀ n m : ℕ, n + m = m + n :=")
    assert induction_like("lemma l : ∀ k : Nat, 0 ≤ k :=")


def test_induction_like_operators():
    assert induction_like("lemma s : Finset.sum (Finset.range n) id = t n :=")
    assert induction_like("lemma p : Finset.prod s f = 0 :=")
    assert induction_like("lemma n : ∑ i in Finset.range n, i = n * (n - 1) / 2 :=")
    assert induction_like("lemma m : ∏ i in s, f i ≠ 0 :=")
    assert induction_like("theorem pow : 2 ^ 10 = 1024 :=")
    assert induction_like("theorem fact (n : ℕ) : 0 < n ! :=")


def test_induction_like_negative():
    assert not induction_like("")
    assert not induction_like("theorem t : 1 + 1 = 2 :=")
    assert not induction_like("lemma z : ∀ x : ℤ, x - x = 0 :=")  # ∀, but not ℕ
    assert not induction_like("lemma q : ∀ v : Naturals, v = v :=")  # not ℕ/Nat


# ---- Config flag ----------------------------------------------------------


def test_config_strengthen_ih_default_off(monkeypatch):
    monkeypatch.delenv("SUBMISSION_STRENGTHEN_IH", raising=False)
    assert Config.from_env().strengthen_ih is False


def test_config_strengthen_ih_env_on(monkeypatch):
    monkeypatch.setenv("SUBMISSION_STRENGTHEN_IH", "1")
    assert Config.from_env().strengthen_ih is True


def test_config_strengthen_ih_only_literal_one_enables(monkeypatch):
    monkeypatch.setenv("SUBMISSION_STRENGTHEN_IH", "0")
    assert Config.from_env().strengthen_ih is False
    monkeypatch.setenv("SUBMISSION_STRENGTHEN_IH", "yes")
    assert Config.from_env().strengthen_ih is False


# ---- shared toolbox fixtures ----------------------------------------------

CHALLENGE = "import Mathlib\n\ntheorem main : 1 + 1 = 2 := by\n  sorry\n"

PARTIAL = """import Mathlib

lemma sum_sq_helper : ∀ n : ℕ, 6 * ∑ i in Finset.range (n + 1), i ^ 2 \
= n * (n + 1) * (2 * n + 1) := by
  sorry

lemma flat_helper : 1 + 1 = 2 := by
  sorry

theorem main : 1 + 1 = 2 := by
  sorry
"""


def make_config(**overrides):
    base = dict(time_limit_s=28800.0, verify_reserve_s=120.0, models="qwen",
                disable_llm=False, qwen_samples=2, gptoss_samples=0,
                repair_rounds=0, sketch_rounds=0, gptoss_call_cap=0,
                fill_breadth=True)  # the promoted from_env default
    base.update(overrides)
    return Config(**base)


def make_toolbox(config, lean=None):
    problem = Problem(id="t", description="d", challenge=CHALLENGE)
    services = Services(llm=None, lean=lean, checkpoint=lambda s, m: None)
    return Toolbox(problem, services, config)


class _AcceptAllLean:
    async def check_file(self, source, *, timeout_s=None):
        return LeanCheck(accepted=True, messages=[], has_sorry="sorry" in source,
                         timed_out=False, duration_ms=1)


class _StallLean:
    """Clean while every sketch sorry is intact; errors on any fill attempt."""

    async def check_file(self, source, *, timeout_s=None):
        clean = source.count("sorry") >= PARTIAL.count("sorry")
        messages = [] if clean else [
            {"severity": "error", "data": "fill rejected",
             "pos": {"line": 1, "col": 0}}]
        return LeanCheck(accepted=False, messages=messages,
                         has_sorry="sorry" in source, timed_out=False,
                         duration_ms=1)


async def _none_sample(model, messages, *, kind, temperature=None):
    return None


async def _dead_sample(model, messages, *, kind, temperature=None):
    raise LLMDead


# ---- strengthen_ih_note: note construction (stubbed toolbox fields) --------


def test_note_appears_with_flag_on_and_two_failures():
    tb = make_toolbox(make_config(strengthen_ih=True))
    tb.last_unfilled = ["flat_helper", "sum_sq_helper"]
    tb.fill_failures = {"sum_sq_helper": 2, "flat_helper": 5}
    note = strengthen_ih_note(tb, PARTIAL)
    assert f"For sum_sq_helper: {STRENGTHEN_MARKER}" in note
    assert "STRONGER induction hypothesis" in note
    assert "then derive the original" in note
    # flat_helper fails often but is not induction-shaped: no advice for it.
    assert "For flat_helper" not in note
    assert any(entry.get("strengthen_ih") == ["sum_sq_helper"]
               for entry in tb.stage_log)


def test_note_empty_with_flag_off():
    tb = make_toolbox(make_config())  # strengthen_ih defaults to off
    tb.last_unfilled = ["sum_sq_helper"]
    tb.fill_failures = {"sum_sq_helper": 9}
    assert strengthen_ih_note(tb, PARTIAL) == ""


def test_note_empty_below_failure_threshold():
    tb = make_toolbox(make_config(strengthen_ih=True))
    tb.last_unfilled = ["sum_sq_helper"]
    tb.fill_failures = {"sum_sq_helper": 1}
    assert strengthen_ih_note(tb, PARTIAL) == ""


def test_note_empty_for_decl_missing_from_source():
    tb = make_toolbox(make_config(strengthen_ih=True))
    tb.last_unfilled = ["ghost_helper"]  # no such decl in the partial file
    tb.fill_failures = {"ghost_helper": 3}
    assert strengthen_ih_note(tb, PARTIAL) == ""


# ---- _fill_one_hole: fill-failure bookkeeping ------------------------------


def test_fill_failures_increment_with_flag_on():
    tb = make_toolbox(make_config(strengthen_ih=True))
    tb.sample = _none_sample
    agent = SubmissionAgent(tb.config)
    assert asyncio.run(agent._fill_one_hole(
        tb, PARTIAL, 0, "sum_sq_helper", tactic_only=True)) is None
    assert tb.fill_failures == {"sum_sq_helper": 1}
    asyncio.run(agent._fill_one_hole(
        tb, PARTIAL, 0, "sum_sq_helper", tactic_only=True))
    assert tb.fill_failures == {"sum_sq_helper": 2}


def test_fill_failures_untouched_with_flag_off():
    tb = make_toolbox(make_config())
    tb.sample = _none_sample
    assert asyncio.run(SubmissionAgent(tb.config)._fill_one_hole(
        tb, PARTIAL, 0, "sum_sq_helper", tactic_only=True)) is None
    assert tb.fill_failures == {}


def test_fill_failures_count_llm_death_as_unclosed():
    tb = make_toolbox(make_config(strengthen_ih=True))
    tb.sample = _dead_sample
    assert asyncio.run(SubmissionAgent(tb.config)._fill_one_hole(
        tb, PARTIAL, 0, "sum_sq_helper", tactic_only=True)) is None
    assert tb.fill_failures == {"sum_sq_helper": 1}


def test_fill_success_does_not_increment():
    tb = make_toolbox(make_config(strengthen_ih=True), lean=_AcceptAllLean())

    async def good_sample(model, messages, *, kind, temperature=None):
        return "```lean\nnorm_num\n```"

    tb.sample = good_sample
    filled = asyncio.run(SubmissionAgent(tb.config)._fill_one_hole(
        tb, PARTIAL, 0, "sum_sq_helper", tactic_only=True))
    assert filled is not None and "norm_num" in filled
    assert tb.fill_failures == {}


# ---- stage4 wiring: the strengthened note reaches the next sketch ----------


def _run_stage4(config, preseed):
    tb = make_toolbox(config, lean=_StallLean())
    tb.fill_failures.update(preseed)
    sketch_calls: list[list[dict[str, str]]] = []
    served = iter(["```lean\n" + PARTIAL + "```"])

    async def fake_sample(model, messages, *, kind, temperature=None):
        if "PROOF SKELETON" in messages[0]["content"]:
            sketch_calls.append(messages)
            return next(served, None)
        return None  # fill dialogues produce nothing usable

    tb.sample = fake_sample
    result = asyncio.run(SubmissionAgent(config).stage4_decompose(tb))
    assert result is None  # stalled decomposition, no accepted proof
    return tb, sketch_calls


def test_stage4_resketch_note_strengthened_with_flag_on():
    # Pre-seed one prior failure; the stalled fill pass adds the second.
    tb, sketch_calls = _run_stage4(
        make_config(strengthen_ih=True, sketch_rounds=2),
        preseed={"sum_sq_helper": 1})
    assert len(sketch_calls) == 2
    resketch = sketch_calls[1][1]["content"]
    assert "replace them with smaller or different lemmas" in resketch
    assert f"For sum_sq_helper: {STRENGTHEN_MARKER}" in resketch
    # Below threshold (1 failure) or not induction-shaped: no advice.
    assert "For flat_helper" not in resketch
    assert "For main" not in resketch
    assert tb.fill_failures["sum_sq_helper"] == 2


def test_stage4_resketch_note_unchanged_with_flag_off():
    tb, sketch_calls = _run_stage4(
        make_config(sketch_rounds=2), preseed={})
    assert len(sketch_calls) == 2
    resketch = sketch_calls[1][1]["content"]
    assert "replace them with smaller or different lemmas" in resketch
    assert STRENGTHEN_MARKER not in resketch
    assert tb.fill_failures == {}  # bookkeeping is flag-guarded too
