import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

-- Helper lemma: 6! < 3^6 (verification that 6 is in the set)
lemma base_case_ineq : Nat.factorial 6 < 3 ^ 6 := by norm_num

-- Helper lemma: base case for induction at n=7
lemma seven_fact_ge_three_pow : Nat.factorial 7 ≥ 3 ^ 7 := by norm_num

-- Helper lemma: inductive step for n ≥ 7
lemma factorial_inductive_step : ∀ k ≥ 7, Nat.factorial k ≥ 3 ^ k → Nat.factorial (k + 1) ≥ 3 ^ (k + 1) := by sorry

-- Helper lemma: for all n ≥ 7, n! ≥ 3^n (proven by induction)
lemma factorial_ge_pow_from_seven : ∀ n ≥ 7, Nat.factorial n ≥ 3 ^ n := by sorry

/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  sorry
