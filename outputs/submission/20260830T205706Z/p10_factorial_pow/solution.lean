import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

/-- Base case: 6! < 3^6 -/
lemma base_case_6 : Nat.factorial 6 < 3 ^ 6 := by norm_num

/-- For any k ≥ 7, we have k! ≥ 3^k -/
lemma factorial_ge_pow_three_at_seven (k : ℕ) (hk : k ≥ 7) : 
    Nat.factorial k ≥ 3 ^ k := by sorry

/-- If k ≥ 7 and k! ≥ 3^k, then (k+1)! ≥ 3^(k+1) -/
lemma factorial_ge_pow_three_inductive_step (k : ℕ) (hk : k ≥ 7) :
    Nat.factorial k ≥ 3 ^ k → Nat.factorial (k + 1) ≥ 3 ^ (k + 1) := by sorry

/-- For any n ≥ 7, we have n! ≥ 3^n by induction -/
lemma factorial_ge_pow_three_for_all_ge_seven (n : ℕ) (hn : n ≥ 7) :
    Nat.factorial n ≥ 3 ^ n := by exact?

/-- Main theorem: p10_answer is the greatest element of the set -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by sorry
