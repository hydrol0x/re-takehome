import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

lemma base_case_6 : Nat.factorial 6 < 3 ^ 6 := by norm_num

/-- For any k ≥ 7, we have k! ≥ 3^k -/
lemma factorial_ge_pow_three_for_all_ge_seven (n : ℕ) (hn : n ≥ 7) :
    Nat.factorial n ≥ 3 ^ n := by sorry

/-- If n! < 3^n then n ≤ 6 -/
lemma factorial_lt_pow_implies_le_six (n : ℕ) (h : Nat.factorial n < 3 ^ n) :
    n ≤ 6 := by sorry

/-- Main theorem: p10_answer is the greatest element of the set -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by sorry
