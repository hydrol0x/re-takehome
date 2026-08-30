import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

/-- Helper: 6! < 3^6 (the answer satisfies the condition) -/
lemma answer_in_set : Nat.factorial 6 < 3 ^ 6 := by norm_num [Nat.factorial]

/-- Helper: 7! > 3^7 (nothing beyond 6 works) -/
lemma seven_not_in_set : ¬(Nat.factorial 7 < 3 ^ 7) := by norm_num [Nat.factorial]

/-- Helper: For any n ≥ 7, n! ≥ 3^n -/
lemma factorial_ge_three_pow_for_ge_seven (n : ℕ) (h : n ≥ 7) : Nat.factorial n ≥ 3 ^ n := by sorry

/-- Main theorem: p10_answer is the greatest element of the set -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by sorry
