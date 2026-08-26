"""Unit tests for the SUBMISSION_SUGGEST_HARVEST branch (B6): per-hole
`apply?` suggestion harvesting in S4 fills."""

from __future__ import annotations

from submission.agent import Config, harvest_try_this


# ---- harvest_try_this (pure parsing) --------------------------------------


def test_harvest_multiple_suggestions_across_messages():
    messages = [
        {"severity": "info", "data": "Try this: exact Nat.le_refl n"},
        {"severity": "info", "data": "Try this: apply Nat.succ_le_succ"},
        {"severity": "error", "data": "unknown identifier 'foo'"},
    ]
    assert harvest_try_this(messages) == [
        "exact Nat.le_refl n",
        "apply Nat.succ_le_succ",
    ]


def test_harvest_multiple_suggestions_in_one_message():
    messages = [{"severity": "info", "data": "Try this: apply f\nTry this: apply g"}]
    assert harvest_try_this(messages) == ["apply f", "apply g"]


def test_harvest_dedupes_preserving_first_seen_order():
    messages = [
        {"data": "Try this: apply And.intro"},
        {"data": "Try this: exact h"},
        {"data": "Try this: apply And.intro"},
        {"data": "Try this:   exact h  "},  # same suggestion, extra whitespace
        {"data": "Try this: omega"},
    ]
    assert harvest_try_this(messages) == ["apply And.intro", "exact h", "omega"]


def test_harvest_no_suggestions():
    assert harvest_try_this([]) == []
    assert harvest_try_this([
        {"severity": "error", "data": "type mismatch"},
        {"severity": "info", "data": ""},
        {},
        {"data": "Try this:   "},  # marker with nothing after it
    ]) == []


# ---- Config flag ----------------------------------------------------------


def test_config_suggest_harvest_default_off(monkeypatch):
    monkeypatch.delenv("SUBMISSION_SUGGEST_HARVEST", raising=False)
    assert Config.from_env().suggest_harvest is False


def test_config_suggest_harvest_on(monkeypatch):
    monkeypatch.setenv("SUBMISSION_SUGGEST_HARVEST", "1")
    assert Config.from_env().suggest_harvest is True


def test_config_suggest_harvest_zero_stays_off(monkeypatch):
    monkeypatch.setenv("SUBMISSION_SUGGEST_HARVEST", "0")
    assert Config.from_env().suggest_harvest is False
