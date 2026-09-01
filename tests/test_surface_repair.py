"""Offline tests for the import-surface fallback (paper §5.4).

Real Config/Toolbox objects, no network, no Docker: covers the Config flag,
the Mathlib-only tactic lint, the confined repair prompt, applicability
gating, and the S5 surface-repair stage with the repair dialogue stubbed.
"""

from re_harness import Problem, Services

from submission.agent import (
    Candidate,
    Config,
    SubmissionAgent,
    Toolbox,
    surface_repair_messages,
)
from submission.lean_text import guard_candidate, parse_challenge, surface_lint

MINIMAL = """import Mathlib.Data.Nat.Basic
import Mathlib.Order.Bounds.Basic

theorem main : 1 + 1 = 2 := by sorry
"""

FULL = """import Mathlib

theorem main : 1 + 1 = 2 := by sorry
"""


def make_config(**overrides) -> Config:
    base = dict(
        time_limit_s=1800.0, verify_reserve_s=120.0, models="duo",
        disable_llm=False, qwen_samples=2, gptoss_samples=1, repair_rounds=2,
        sketch_rounds=1, gptoss_call_cap=4,
    )
    base.update(overrides)
    return Config(**base)


def make_agent_and_toolbox(challenge: str = MINIMAL, **overrides):
    config = make_config(**overrides)
    problem = Problem(id="t", description="d", challenge=challenge)
    services = Services(llm=None, lean=None, checkpoint=lambda s, m: None)
    return SubmissionAgent(config), Toolbox(problem, services, config)


# ---- Config flag -----------------------------------------------------------


def test_flag_on_by_default(monkeypatch):
    monkeypatch.delenv("SUBMISSION_SURFACE_REPAIR", raising=False)
    assert Config.from_env().surface_repair is True


def test_flag_zero_disables(monkeypatch):
    monkeypatch.setenv("SUBMISSION_SURFACE_REPAIR", "0")
    assert Config.from_env().surface_repair is False


# ---- lint -------------------------------------------------------------------


def test_lint_flags_mathlib_only_tactics():
    assert surface_lint("theorem t : 1 = 1 := by\n  norm_num\n") == "norm_num"
    assert surface_lint("  interval_cases a <;> omega\n") == "interval_cases"
    assert surface_lint("  nlinarith [sq_nonneg a]\n") == "nlinarith"
    assert surface_lint("  ring\n") == "ring"


def test_lint_accepts_core_only_proofs():
    core = ("  obtain ⟨a, b, ha, hb, hdvd, heq⟩ := hn\n  subst heq\n"
            "  rcases Nat.lt_or_ge (a * b) 10 with hlt | hge\n"
            "  · exfalso\n    have key : ∀ a' < 10, P a' := by decide\n    omega\n"
            "  · exact hge\n")
    assert surface_lint(core) == ""


def test_lint_ignores_comments_and_identifier_prefixes():
    assert surface_lint("  -- we avoid norm_num here\n  omega\n") == ""
    assert surface_lint("  exact ring_hom_lemma h\n") == ""  # `ring` inside a longer identifier
    assert surface_lint("  exact Nat.ring_stuff\n") == ""


# ---- prompt -----------------------------------------------------------------


def test_surface_prompt_pins_imports_and_forbids_tactics():
    problem = Problem(id="t", description="d", challenge=MINIMAL)
    imports = ["import Mathlib.Data.Nat.Basic", "import Mathlib.Order.Bounds.Basic"]
    messages = surface_repair_messages(problem, MINIMAL, imports,
                                       feedback="error: Solution.lean:5:2: unknown tactic")
    system, user = messages[0]["content"], messages[1]["content"]
    assert "import Mathlib.Data.Nat.Basic" in system
    assert "import Mathlib.Order.Bounds.Basic" in system
    assert "norm_num" in system and "interval_cases" in system
    assert "decide" in system  # the bounded-exhaustion technique
    assert "unknown tactic" in user
    assert "byte-for-byte" in system  # RULES_BLOCK still applies


# ---- applicability ----------------------------------------------------------


def test_applicable_only_on_minimal_import_challenges():
    agent, tb = make_agent_and_toolbox(MINIMAL)
    assert agent._surface_repair_applicable(tb)
    agent_full, tb_full = make_agent_and_toolbox(FULL)
    assert not agent_full._surface_repair_applicable(tb_full)
    agent_off, tb_off = make_agent_and_toolbox(MINIMAL, surface_repair=False)
    assert not agent_off._surface_repair_applicable(tb_off)


def test_not_applicable_when_channels_dead():
    agent, tb = make_agent_and_toolbox(MINIMAL)
    tb.llm_alive = False
    assert not agent._surface_repair_applicable(tb)


# ---- stage ------------------------------------------------------------------


async def test_stage_confines_repair_and_returns_result():
    agent, tb = make_agent_and_toolbox(MINIMAL)
    winner = Candidate(source=MINIMAL.replace("sorry", "norm_num"), origin="qwen-fast:s1",
                       accepted=True, error_count=0)
    seen = {}

    async def fake_repair(tb_, candidate, *, origin_model, build_messages, guard, stage,
                          success=None):
        seen["stage"] = stage
        seen["origin_model"] = origin_model
        seen["feedback_in_prompt"] = (
            "unknown tactic" in build_messages("error: unknown tactic 'norm_num'")[1]["content"])
        # The guard must reject Mathlib-only tactics and accept core proofs,
        # composing both on the challenge's import block.
        seen["rejects_norm_num"] = guard(MINIMAL.replace("sorry", "norm_num")) is None
        core = guard("theorem main : 1 + 1 = 2 := by\n  decide\n")
        seen["core_kept"] = core is not None and core.startswith("import Mathlib.Data.Nat.Basic")
        return Candidate(source=core, origin="qwen:s5-surface:r1", accepted=True, error_count=0)

    agent.repair_with_handoff = fake_repair
    result = await agent.stage5_surface_repair(
        tb, winner, "Building Solution\nerror: Solution.lean:5:2: unknown tactic 'norm_num'\n")
    assert result is not None and result.origin == "qwen:s5-surface:r1"
    assert seen == {"stage": "S5-surface", "origin_model": "qwen/qwen3.5-flash-02-23",
                    "feedback_in_prompt": True, "rejects_norm_num": True, "core_kept": True}


async def test_stage_swallows_repair_errors():
    agent, tb = make_agent_and_toolbox(MINIMAL)
    winner = Candidate(source=MINIMAL.replace("sorry", "decide"), origin="gptoss:s1",
                       accepted=True, error_count=0)

    async def broken_repair(*args, **kwargs):
        raise RuntimeError("boom")

    agent.repair_with_handoff = broken_repair
    assert await agent.stage5_surface_repair(tb, winner, "error: x") is None


def test_guard_composition_makes_added_tactic_imports_moot():
    parsed = parse_challenge(MINIMAL)
    with_extra = MINIMAL.replace("sorry", "decide").replace(
        "import Mathlib.Order.Bounds.Basic", "import Mathlib.Order.Bounds.Basic\nimport Mathlib.Tactic")
    guarded, _ = guard_candidate(with_extra, parsed)
    assert guarded is not None and "Mathlib.Tactic" not in guarded


# ---- surface mode: continuation after a failed confined round ---------------


def test_toolbox_guard_lints_only_in_surface_mode():
    _agent, tb = make_agent_and_toolbox(MINIMAL)
    proof = MINIMAL.replace("sorry", "norm_num")
    assert tb.guard(proof) is not None          # normal mode: composition only
    assert tb.surface_imports is None
    tb.surface_mode = True
    assert tb.surface_imports == ["import Mathlib.Data.Nat.Basic",
                                  "import Mathlib.Order.Bounds.Basic"]
    assert tb.guard(proof) is None              # surface mode: Mathlib-only tactic rejected
    assert tb.guard(MINIMAL.replace("sorry", "decide")) is not None


def test_whole_proof_prompt_carries_surface_block_only_when_asked():
    from submission.agent import whole_proof_messages
    problem = Problem(id="t", description="d", challenge=MINIMAL)
    plain = whole_proof_messages(problem, MINIMAL)[0]["content"]
    assert "restricted import surface" not in plain
    surfaced = whole_proof_messages(
        problem, MINIMAL, surface=["import Mathlib.Data.Nat.Basic"])[0]["content"]
    assert "restricted import surface" in surfaced
    assert "import Mathlib.Data.Nat.Basic" in surfaced
    assert "interval_cases" in surfaced and "decide" in surfaced
