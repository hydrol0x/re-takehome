import Mathlib

-- ----------------------------------------------------------------------
-- Helper lemmas (easy, left with `linarith` for the skeleton)
-- ----------------------------------------------------------------------

/-- If `n ≤ 6` then `n! < 3 ^ n`. -/
lemma factorial_lt_three_pow_of_le6 (n : ℕ) (hn : n ≤ 6) :
    Nat.factorial n < 3 ^ n := by
  sorry

/-- If `7 ≤ n` then `3 ^ n ≤ n!`. -/
lemma three_pow_le_factorial_of_ge7 (n : ℕ) (hn : 7 ≤ n) :
    3 ^ n ≤ Nat.factorial n := by
  sorry

-- ----------------------------------------------------------------------
-- Answer and main theorem
-- ----------------------------------------------------------------------

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  -- `p10_answer` belongs to the set
  have h_mem : p10_answer ∈ {n : ℕ | Nat.factorial n < 3 ^ n} := by
    have hle : (p10_answer : ℕ) ≤ 6 := by
      simpa [p10_answer]
    have hlt := factorial_lt_three_pow_of_le6 p10_answer hle
    simpa [p10_answer] using hlt
  refine ⟨h_mem, ?_⟩
  intro n hn
  by_cases h7 : 7 ≤ n
  · -- contradiction with the upper bound for `n ≥ 7`
    have hcontr : Nat.factorial n < Nat.factorial n :=
      Nat.lt_of_lt_of_le hn (three_pow_le_factorial_of_ge7 n h7)
    exact (False.elim ((lt_irrefl _) hcontr))
  · -- therefore `n < 7`, i.e. `n ≤ 6`
    have hlt : n < 7 := Nat.lt_of_not_ge h7
    exact Nat.le_of_lt_succ hlt
