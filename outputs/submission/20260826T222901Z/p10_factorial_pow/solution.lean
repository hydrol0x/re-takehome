import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

/-- Helper: For all n ≥ 7, n! ≥ 3^n -/
lemma factorial_ge_pow_three (n : ℕ) (h : 7 ≤ n) : Nat.factorial n ≥ 3 ^ n := by
  sorry

/-- Base case: 6! < 3^6 -/
lemma base_case : Nat.factorial 6 < 3 ^ 6 := by decide

/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  sorry
