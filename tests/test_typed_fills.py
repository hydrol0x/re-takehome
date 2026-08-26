"""Offline tests for SUBMISSION_TYPED_FILLS (research branch B4).

Covers the Config flag wiring, the goal-class technique table, the
flag-guarded injection point in `fill_messages`, and `_fill_one_hole`
passing the class block through (byte-identical prompts when off).
"""

from re_harness import Problem, Services

from submission.agent import (
    FILL_TECHNIQUES,
    Config,
    SubmissionAgent,
    Toolbox,
    fill_messages,
)
from submission.lean_text import classify_goal

CHALLENGE = "import Mathlib\n\ntheorem tf : ∀ n : ℕ, n + 0 = n := by\n  sorry\n"
PROBLEM = Problem(id="t", description="Show it.", challenge=CHALLENGE)


# ---- Config flag ---------------------------------------------------------


def test_config_typed_fills_default_off(monkeypatch):
    monkeypatch.delenv("SUBMISSION_TYPED_FILLS", raising=False)
    assert Config.from_env().typed_fills is False


def test_config_typed_fills_env_on(monkeypatch):
    monkeypatch.setenv("SUBMISSION_TYPED_FILLS", "1")
    assert Config.from_env().typed_fills is True


def test_config_typed_fills_only_literal_one_enables(monkeypatch):
    for raw in ("0", "", " ", "yes"):
        monkeypatch.setenv("SUBMISSION_TYPED_FILLS", raw)
        assert Config.from_env().typed_fills is False


# ---- technique table -----------------------------------------------------


def test_technique_table_covers_every_class():
    representatives = {
        "induction": "theorem a : ∀ n : ℕ, n + 0 = n :=",
        "divisibility": "theorem b (n : ℕ) : 3 ∣ n * 3 :=",
        "inequality": "theorem c (a : ℤ) : a ≤ a + 1 :=",
        "cast": "theorem d (k : ℕ) : (↑k : ℝ) = ↑k :=",
        "arith": "theorem e : 2 + 2 = 4 :=",
    }
    assert set(FILL_TECHNIQUES) == set(representatives)
    for cls, statement in representatives.items():
        assert classify_goal(statement) == cls
    for cls, block in FILL_TECHNIQUES.items():
        assert block.startswith("Goal-class hints"), cls
        assert 4 <= len(block.splitlines()) <= 6, cls
        for banned in ("sorry", "admit", "native_decide ", "axiom "):
            assert banned not in block, (cls, banned)


# ---- fill_messages injection point ---------------------------------------


def test_fill_messages_without_technique_byte_identical():
    default = fill_messages(PROBLEM, CHALLENGE, "tf")
    explicit = fill_messages(PROBLEM, CHALLENGE, "tf", technique="")
    assert default == explicit  # flag-off path: byte-identical prompt
    assert "Goal-class hints" not in explicit[1]["content"]


def test_fill_messages_appends_technique_block():
    block = FILL_TECHNIQUES["induction"]
    baseline = fill_messages(PROBLEM, CHALLENGE, "tf")
    messages = fill_messages(PROBLEM, CHALLENGE, "tf", technique=block)
    assert messages[0] == baseline[0]  # system prompt untouched
    assert messages[1]["content"] == baseline[1]["content"] + "\n\n" + block


def test_fill_messages_technique_follows_feedback():
    block = FILL_TECHNIQUES["arith"]
    messages = fill_messages(PROBLEM, CHALLENGE, "tf", feedback="err",
                             technique=block)
    content = messages[1]["content"]
    assert content.endswith("\n\n" + block)
    assert content.index("Lean feedback") < content.index(block)


# ---- _fill_one_hole wiring (offline, stubbed tb.sample) ------------------


def make_config(**overrides):
    base = dict(time_limit_s=28800.0, verify_reserve_s=120.0, models="qwen",
                disable_llm=False, qwen_samples=1, gptoss_samples=0,
                repair_rounds=0, sketch_rounds=0, gptoss_call_cap=0)
    base.update(overrides)
    return Config(**base)


async def run_fill(config, decl_name="tf"):
    problem = Problem(id="t", description="Show it.", challenge=CHALLENGE)
    services = Services(llm=None, lean=None, checkpoint=lambda s, m: None)
    tb = Toolbox(problem, services, config)
    seen: list[list[dict]] = []

    async def fake_sample(model, messages, *, kind, temperature=None):
        seen.append(messages)
        return None  # no candidate blocks: dialogue cycles, no lean needed

    tb.sample = fake_sample
    result = await SubmissionAgent(config)._fill_one_hole(
        tb, CHALLENGE, 0, decl_name, tactic_only=False)
    assert result is None
    return problem, seen


async def test_fill_one_hole_flag_on_appends_class_block():
    _, seen = await run_fill(make_config(typed_fills=True))
    assert seen  # the dialogue ran
    assert classify_goal("theorem tf : ∀ n : ℕ, n + 0 = n :=") == "induction"
    block = FILL_TECHNIQUES["induction"]
    for messages in seen:
        assert messages[1]["content"].endswith("\n\n" + block)


async def test_fill_one_hole_flag_on_first_prompt_exact():
    problem, seen = await run_fill(make_config(typed_fills=True))
    expected = fill_messages(problem, CHALLENGE, "tf",
                             technique=FILL_TECHNIQUES["induction"])
    assert seen[0] == expected


async def test_fill_one_hole_flag_off_prompt_byte_identical():
    problem, seen = await run_fill(make_config())  # typed_fills defaults off
    assert seen
    assert seen[0] == fill_messages(problem, CHALLENGE, "tf")  # byte-compare
    for messages in seen:
        assert "Goal-class hints" not in messages[1]["content"]


async def test_fill_one_hole_flag_on_unknown_decl_leaves_prompt_alone():
    problem, seen = await run_fill(make_config(typed_fills=True),
                                   decl_name="ghost")
    assert seen
    assert seen[0] == fill_messages(problem, CHALLENGE, "ghost")
    for messages in seen:
        assert "Goal-class hints" not in messages[1]["content"]
