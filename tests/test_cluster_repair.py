"""Offline tests for SUBMISSION_CLUSTER_REPAIR (research branch B3).

Mirrors tests/test_wave_spread.py: real Config/Toolbox objects, no network;
LLM, lean, and the repair dialogue itself stubbed out. Covers the pure
`transfer_fix` and `cluster_near_misses` helpers, the Config flag wiring,
and the flag-guarded S2 target selection / sibling-transfer plumbing.
"""

from re_harness import Problem, Services

from submission.agent import (
    Candidate,
    Config,
    SubmissionAgent,
    Toolbox,
    cluster_near_misses,
    transfer_fix,
)

CHALLENGE = """import Mathlib

theorem main : 1 + 1 = 2 := by sorry
"""

REP_FAILED = """import Mathlib

theorem main : 1 + 1 = 2 := by
  nlinarith
"""

REP_REPAIRED = """import Mathlib

theorem main : 1 + 1 = 2 := by
  norm_num
"""


def sibling_source(tag: str, tactic: str = "nlinarith") -> str:
    return (f"import Mathlib\n\n-- attempt {tag}\n"
            f"theorem main : 1 + 1 = 2 := by\n  {tactic}\n")


# ---- Config flag plumbing --------------------------------------------------


def test_flag_off_by_default(monkeypatch):
    monkeypatch.delenv("SUBMISSION_CLUSTER_REPAIR", raising=False)
    assert Config.from_env().cluster_repair is False


def test_flag_on(monkeypatch):
    monkeypatch.setenv("SUBMISSION_CLUSTER_REPAIR", "1")
    assert Config.from_env().cluster_repair is True


def test_flag_non_1_values_stay_off(monkeypatch):
    for raw in ("0", "", " ", "yes"):
        monkeypatch.setenv("SUBMISSION_CLUSTER_REPAIR", raw)
        assert Config.from_env().cluster_repair is False


# ---- transfer_fix: pure single-block transplant ----------------------------


def test_transfer_single_line_replace():
    patched = transfer_fix(REP_FAILED, REP_REPAIRED, sibling_source("a"))
    assert patched == sibling_source("a", tactic="norm_num")


def test_transfer_multi_line_block_and_growth():
    failed = "a\nx\ny\nd\n"
    repaired = "a\np\nq\nr\nd\n"  # 2 lines -> 3 lines, one contiguous block
    sibling = "s0\nx\ny\nd\ntail\n"
    assert transfer_fix(failed, repaired, sibling) == "s0\np\nq\nr\nd\ntail\n"


def test_transfer_replaces_first_occurrence_only():
    assert transfer_fix("a\nx\nb\n", "a\ny\nb\n", "x\nmid\nx\n") == "y\nmid\nx\n"


def test_transfer_preserves_missing_trailing_newline():
    assert transfer_fix("a\nx\nb\n", "a\ny\nb\n", "pre\nx\nb") == "pre\ny\nb"


def test_transfer_multi_block_diff_is_none():
    failed = "a\nx\nb\nc\nz\nd\n"
    repaired = "a\nX\nb\nc\nZ\nd\n"  # two separated replaced blocks
    assert transfer_fix(failed, repaired, failed) is None


def test_transfer_block_absent_is_none():
    assert transfer_fix(REP_FAILED, REP_REPAIRED, sibling_source("a", "ring_nf")) is None


def test_transfer_insert_only_diff_is_none():
    # e.g. the deterministic set_option preamble fix: pure insertion.
    assert transfer_fix("a\nb\n", "a\nnew\nb\n", "a\nb\n") is None


def test_transfer_delete_only_diff_is_none():
    assert transfer_fix("a\ngone\nb\n", "a\nb\n", "a\ngone\nb\n") is None


def test_transfer_identical_sources_is_none():
    assert transfer_fix(REP_FAILED, REP_FAILED, sibling_source("a")) is None


# ---- cluster_near_misses: grouping and order -------------------------------


def near_miss(error_head: str, errors: int, tag: str = "x",
              tactic: str = "nlinarith") -> Candidate:
    candidate = Candidate(source=sibling_source(tag, tactic), origin="qwen-fast:s1")
    candidate.error_count = errors
    candidate.messages = [{"severity": "error", "data": error_head}]
    return candidate


def test_cluster_order_and_representatives():
    a1 = near_miss("unknown identifier 'foo'", 4, "a1")
    a2 = near_miss("unknown identifier 'foo'", 2, "a2")
    a3 = near_miss("unknown identifier 'foo'", 7, "a3")
    b1 = near_miss("type mismatch at main", 1, "b1")
    c1 = near_miss("linarith failed", 3, "c1")
    c2 = near_miss("linarith failed", 3, "c2")
    clusters = cluster_near_misses([b1, a1, c1, a2, c2, a3])
    assert clusters == [[a2, a1, a3], [c1, c2], [b1]]  # largest first
    assert clusters[0][0] is a2      # representative: fewest errors in cluster
    assert clusters[1] == [c1, c2]   # equal errors: stable input order


def test_cluster_equal_sizes_keep_first_seen_order():
    b = near_miss("beta", 1, "b")
    a = near_miss("alpha", 2, "a")
    assert cluster_near_misses([b, a]) == [[b], [a]]
    assert cluster_near_misses([a, b]) == [[a], [b]]


def test_cluster_empty_input():
    assert cluster_near_misses([]) == []


# ---- stage2 wiring (offline, stubbed repair dialogue and REPL) -------------


def make_config(**overrides):
    base = dict(time_limit_s=28800.0, verify_reserve_s=120.0, models="qwen",
                disable_llm=False, qwen_samples=2, gptoss_samples=0,
                repair_rounds=1, sketch_rounds=0, gptoss_call_cap=0)
    base.update(overrides)
    return Config(**base)


def make_agent_and_toolbox(**overrides):
    config = make_config(**overrides)
    problem = Problem(id="t", description="d", challenge=CHALLENGE)
    services = Services(llm=None, lean=None, checkpoint=lambda s, m: None)
    return SubmissionAgent(config), Toolbox(problem, services, config)


def stub_stage2(agent, tb, repair_results):
    """Stub the repair dialogue, the REPL check, and the LLM channel.

    Returns (repaired_targets, checked_sources): who S2 chose to repair, and
    which sources the sibling-transfer path sent to tb.check.
    """

    targets: list[Candidate] = []
    checked: list[str] = []
    results = iter(repair_results)

    async def fake_repair(tb_, candidate, **kwargs):
        targets.append(candidate)
        return next(results, None)

    async def fake_check(candidate, timeout_s=90):
        checked.append(candidate.source)
        candidate.accepted = True
        candidate.error_count = 0
        candidate.sorry_count = 0
        return candidate

    async def no_sample(*args, **kwargs):
        raise AssertionError("cluster bookkeeping must not add LLM calls")

    agent.repair_with_handoff = fake_repair
    tb.check = fake_check
    tb.sample = no_sample
    return targets, checked


def cluster_fixture():
    """Three clusters: sizes 3 (nlinarith), 2 (omega), 1 — scrambled order."""

    rep = Candidate(source=REP_FAILED, origin="qwen-fast:s1")
    rep.error_count = 1
    rep.messages = [{"severity": "error", "data": "unknown identifier 'foo'"}]
    sib1 = near_miss("unknown identifier 'foo'", 2, "s1")
    sib2 = near_miss("unknown identifier 'foo'", 3, "s2")
    c1 = near_miss("linarith failed", 3, "c1", tactic="omega")
    c2 = near_miss("linarith failed", 4, "c2", tactic="omega")
    b1 = near_miss("type mismatch at main", 2, "b1", tactic="decide")
    return rep, c1, [sib2, c1, b1, rep, c2, sib1]


async def test_flag_on_repairs_representatives_largest_cluster_first():
    agent, tb = make_agent_and_toolbox(cluster_repair=True)
    rep, c_rep, candidates = cluster_fixture()
    targets, checked = stub_stage2(agent, tb, [None, None])
    assert await agent.stage2_repair(tb, candidates) is None
    # Budget still 2 dialogues: cluster-of-3's rep, then cluster-of-2's rep;
    # the singleton cluster (b1) never gets a dialogue.
    assert targets == [rep, c_rep]
    assert checked == []  # failed repairs transfer nothing


async def test_flag_off_selection_is_unchanged_and_transfers_nothing():
    agent, tb = make_agent_and_toolbox()  # cluster_repair defaults to False
    rep, _c_rep, candidates = cluster_fixture()
    accepted = Candidate(source=REP_REPAIRED, origin="qwen:s2:r1", accepted=True,
                         error_count=0)
    targets, checked = stub_stage2(agent, tb, [accepted])
    assert await agent.stage2_repair(tb, candidates) is accepted
    # Today's order: top-2 by global error count (stable) — rep(1), then sib1/b1(2).
    assert targets == [rep]  # first target's repair succeeded; loop returned
    assert checked == []     # no transfer machinery when the flag is off


async def test_flag_off_picks_top_two_by_error_count():
    agent, tb = make_agent_and_toolbox()
    _rep, _c_rep, candidates = cluster_fixture()
    targets, _checked = stub_stage2(agent, tb, [None, None])
    assert await agent.stage2_repair(tb, candidates) is None
    assert [t.error_count for t in targets] == [1, 2]
    assert targets == sorted(candidates, key=lambda c: c.error_count)[:2]


async def test_flag_on_success_transfers_to_siblings():
    agent, tb = make_agent_and_toolbox(cluster_repair=True)
    rep, _c_rep, candidates = cluster_fixture()
    accepted = Candidate(source=REP_REPAIRED, origin="qwen:s2:r1", accepted=True,
                         error_count=0)
    targets, checked = stub_stage2(agent, tb, [accepted])
    assert await agent.stage2_repair(tb, candidates) is accepted
    assert targets == [rep]
    # Both siblings patched (nlinarith -> norm_num) and REPL-checked, in
    # ascending-error order; accepted transfers are recorded as best.
    assert checked == [sibling_source("s1", "norm_num"),
                       sibling_source("s2", "norm_num")]
    assert tb.best.accepted and tb.best.origin.endswith(":transfer")


async def test_flag_on_transfer_caps_at_three_siblings():
    agent, tb = make_agent_and_toolbox(cluster_repair=True)
    rep = Candidate(source=REP_FAILED, origin="qwen-fast:s1")
    rep.error_count = 1
    rep.messages = [{"severity": "error", "data": "unknown identifier 'foo'"}]
    sibs = [near_miss("unknown identifier 'foo'", 2 + i, f"s{i}") for i in range(4)]
    accepted = Candidate(source=REP_REPAIRED, origin="qwen:s2:r1", accepted=True,
                         error_count=0)
    _targets, checked = stub_stage2(agent, tb, [accepted])
    assert await agent.stage2_repair(tb, [rep] + sibs) is accepted
    assert checked == [sibling_source(f"s{i}", "norm_num") for i in range(3)]


async def test_flag_on_transfer_skips_sibling_without_the_block():
    agent, tb = make_agent_and_toolbox(cluster_repair=True)
    rep = Candidate(source=REP_FAILED, origin="qwen-fast:s1")
    rep.error_count = 1
    rep.messages = [{"severity": "error", "data": "unknown identifier 'foo'"}]
    absent = near_miss("unknown identifier 'foo'", 2, "s0", tactic="ring_nf")
    present = near_miss("unknown identifier 'foo'", 3, "s1")
    accepted = Candidate(source=REP_REPAIRED, origin="qwen:s2:r1", accepted=True,
                         error_count=0)
    _targets, checked = stub_stage2(agent, tb, [accepted])
    assert await agent.stage2_repair(tb, [rep, absent, present]) is accepted
    assert checked == [sibling_source("s1", "norm_num")]


async def test_flag_on_transfer_respects_deadline():
    agent, tb = make_agent_and_toolbox(cluster_repair=True)
    rep, _c_rep, candidates = cluster_fixture()
    accepted = Candidate(source=REP_REPAIRED, origin="qwen:s2:r1", accepted=True,
                         error_count=0)
    _targets, checked = stub_stage2(agent, tb, [accepted])
    tb.deadline.allows = lambda seconds: False  # type: ignore[method-assign]
    assert await agent.stage2_repair(tb, candidates) is accepted
    assert checked == []
