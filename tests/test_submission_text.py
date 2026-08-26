"""Offline tests for submission.lean_text (no Docker, no network)."""

from pathlib import Path

from submission.lean_text import (
    bounded_intro_templates,
    error_signature,
    eval_nat_literal,
    extract_lean,
    guard_candidate,
    insert_preamble,
    normalize_numeric_answers,
    parse_challenge,
    splice_holes,
    splice_tactics,
)

SAMPLES = Path(__file__).resolve().parents[1] / "sample-problems"


def test_parse_all_sample_challenges():
    for problem_dir in sorted(SAMPLES.iterdir()):
        challenge = problem_dir / "challenge.lean"
        if not challenge.is_file():
            continue
        parsed = parse_challenge(challenge.read_text())
        assert parsed.holes, problem_dir.name
        assert parsed.decl_names, problem_dir.name
        assert parsed.signatures, problem_dir.name


def test_numeric_answer_detection():
    parsed = parse_challenge((SAMPLES / "p06_pow_mod" / "challenge.lean").read_text())
    assert parsed.numeric_answer_names == ["p06_answer"]
    assert parsed.has_term_holes


def test_splice_preserves_statements():
    source = (SAMPLES / "p09_imo1964" / "challenge.lean").read_text()
    spliced = splice_tactics(source, "omega")
    assert spliced is not None
    assert spliced.count("omega") == 2  # both holes
    before = parse_challenge(source)
    after = parse_challenge(spliced)
    assert before.signatures == after.signatures


def test_splice_refuses_term_holes():
    source = (SAMPLES / "p06_pow_mod" / "challenge.lean").read_text()
    assert splice_tactics(source, "norm_num") is None


def test_splice_single_hole():
    source = "import Mathlib\n\ntheorem t : 1 = 1 := by\n  sorry\n\ntheorem u : 2 = 2 := by\n  sorry\n"
    out = splice_holes(source, {1: "rfl"})
    assert "sorry" in out and "rfl" in out
    assert out.index("sorry") < out.index("rfl")


def test_guard_rejects_banned_tokens():
    parsed = parse_challenge("import Mathlib\ntheorem t : 1 = 1 := by\n  sorry\n")
    for bad in ["by native_decide", "by admit", "by sorry"]:
        candidate = f"import Mathlib\ntheorem t : 1 = 1 := {bad}\n"
        guarded, reason = guard_candidate(candidate, parsed)
        assert guarded is None, bad
    for prefix in ["axiom", "private axiom", "@[simp] axiom"]:
        candidate = (f"import Mathlib\n{prefix} evil : False\n"
                     "theorem t : 1 = 1 := by exact rfl\n")
        guarded, reason = guard_candidate(candidate, parsed)
        assert guarded is None, prefix
    # the word inside a comment must not trip the guard
    commented = ("import Mathlib\n-- we avoid the axiom of choice here\n"
                 "theorem t : 1 = 1 := by exact rfl\n")
    guarded, _ = guard_candidate(commented, parsed)
    assert guarded is not None


def test_guard_rejects_altered_statement():
    source = (SAMPLES / "p01_linear" / "challenge.lean").read_text()
    parsed = parse_challenge(source)
    altered = source.replace("x = 5", "x = 6").replace("sorry", "norm_num")
    guarded, reason = guard_candidate(altered, parsed)
    assert guarded is None
    assert "statement" in reason


def test_guard_accepts_whitespace_variation():
    source = (SAMPLES / "p01_linear" / "challenge.lean").read_text()
    parsed = parse_challenge(source)
    candidate = source.replace("sorry", "linarith").replace("3 * x + 7", "3 * x  + 7")
    guarded, _ = guard_candidate(candidate, parsed)
    assert guarded is not None


def test_numeric_literal_normalization():
    parsed = parse_challenge((SAMPLES / "p06_pow_mod" / "challenge.lean").read_text())
    candidate = (
        "import Mathlib\n\nabbrev p06_answer : ℕ := 7 ^ 2 % 100\n\n"
        "theorem p06_pow_mod : 7 ^ 2026 % 100 = p06_answer := by\n  norm_num\n"
    )
    guarded, _ = guard_candidate(candidate, parsed)
    assert guarded is not None
    assert "abbrev p06_answer : ℕ := 49" in guarded


def test_eval_nat_literal():
    assert eval_nat_literal("2^11 - 1") == 2047
    assert eval_nat_literal("(3 + 4) * 7") == 49
    assert eval_nat_literal("x + 1") is None
    assert eval_nat_literal("10^100000") is None  # power guard
    assert eval_nat_literal("2 - 5") is None  # negative


def test_extract_lean_prefers_last_fence():
    text = "```lean\nfirst\n```\nprose\n```lean\nimport Mathlib\nsecond\n```"
    assert "second" in extract_lean(text)


def test_insert_preamble_after_imports():
    out = insert_preamble("import Mathlib\n\ntheorem t : 1 = 1 := by rfl\n", "set_option x 1")
    assert out.splitlines()[0] == "import Mathlib"
    assert "set_option x 1" in out.splitlines()[2]


def test_error_signature_stability():
    msgs_a = [{"severity": "error", "data": "unsolved goals\nfoo"}]
    msgs_b = [{"severity": "error", "data": "unsolved goals\nbar"}]
    msgs_c = [{"severity": "error", "data": "Unknown constant blah"}]
    assert error_signature(msgs_a) == error_signature(msgs_b)
    assert error_signature(msgs_a) != error_signature(msgs_c)


def test_bounded_templates_arrow_le():
    scripts = bounded_intro_templates("theorem f : ∀ n, n ≤ 12 → 2 * n ≤ 24 :=")
    assert scripts[0] == "intro n hn\ninterval_cases n <;> omega"
    assert "intro n hn\ninterval_cases n <;> decide" in scripts
    assert 2 <= len(scripts) <= 4
    assert all(script.startswith("intro n hn\n") for script in scripts)


def test_bounded_templates_arrow_lt_and_ascription():
    scripts = bounded_intro_templates("lemma g : ∀ m, m < 100 → m % 100 = m :=")
    assert scripts and all(script.startswith("intro m hm\n") for script in scripts)
    assert "interval_cases m <;> omega" in scripts[0]
    ascribed = bounded_intro_templates("theorem f : ∀ n : ℕ, n ≤ 5 → n ≤ 6 :=")
    assert ascribed and ascribed[0] == "intro n hn\ninterval_cases n <;> omega"


def test_bounded_templates_binder_forms():
    for statement in ["theorem f : ∀ n < 100, n * 0 = 0 :=",
                      "theorem f : ∀ n ≤ 12, n ≤ 20 :="]:
        scripts = bounded_intro_templates(statement)
        assert scripts, statement
        assert scripts[0] == "intro n hn\ninterval_cases n <;> omega"
        assert 2 <= len(scripts) <= 4
    primed = bounded_intro_templates("lemma h : ∀ k' < 9, k' ≤ 9 :=")
    assert primed and primed[0].startswith("intro k' hk'\n")


def test_bounded_templates_finset_range():
    scripts = bounded_intro_templates("theorem f : ∀ p ∈ Finset.range 50, p < 50 :=")
    assert 2 <= len(scripts) <= 4
    for script in scripts:
        lines = script.splitlines()
        assert lines[0] == "intro p hp"
        assert lines[1] == "simp only [Finset.mem_range] at hp"
        assert lines[2].startswith("interval_cases p <;> ")


def test_bounded_templates_bound_cap():
    assert bounded_intro_templates("theorem f : ∀ n, n ≤ 301 → True :=") == []
    assert bounded_intro_templates("theorem f : ∀ n, n ≤ 300 → True :=") != []
    assert bounded_intro_templates("theorem f : ∀ n < 40, True :=", max_bound=30) == []
    assert bounded_intro_templates("theorem f : ∀ n ∈ Finset.range 999, True :=") == []


def test_bounded_templates_no_match():
    for statement in [
        "theorem f : 1 + 1 = 2 :=",                    # no ∀ at all
        "theorem f : ∀ n, n * 0 = 0 :=",               # unbounded ∀
        "theorem f : ∀ n, m ≤ 12 → n = n :=",          # bound names another var
        "theorem f : ∀ n, n ≤ k → n = n :=",           # bound is not a numeral
        "theorem f : ∀ n ∈ Finset.Icc 1 9, n ≤ 9 :=",  # unsupported set
        "theorem f : ∀ n > 0, n + 1 > 1 :=",           # lower bound, not upper
    ]:
        assert bounded_intro_templates(statement) == [], statement


def test_bounded_templates_weird_spacing():
    scripts = bounded_intro_templates("theorem  f :  ∀  n ,\n  n  ≤  12  →  n = n  :=")
    assert scripts and scripts[0] == "intro n hn\ninterval_cases n <;> omega"
    tight = bounded_intro_templates("theorem f : ∀ n<7, n ≤ 7 :=")
    assert tight and tight[0] == "intro n hn\ninterval_cases n <;> omega"


def test_bounded_templates_from_parsed_signature():
    source = "import Mathlib\n\ntheorem tiny : ∀ n < 10, n + 0 = n := by\n  sorry\n"
    parsed = parse_challenge(source)
    scripts = bounded_intro_templates(parsed.signatures[0])
    assert scripts and scripts[0] == "intro n hn\ninterval_cases n <;> omega"
