import Mathlib

/-- The largest `k` such that `3 ^ k ∣ 100!`. Must be a numeric literal. -/
abbrev h01_answer : ℕ := 48

/-- Helper lemma: Legendre's formula gives v₃(100!) = 48 -/
lemma v3_factorial_100_eq_48 : 
    padicValNat 3 (Nat.factorial 100) = 48 := by sorry

/-- Helper: 3^48 divides 100! -/
lemma three_pow_48_dvd_factorial_100 : 
    3 ^ 48 ∣ Nat.factorial 100 := by norm_num

/-- Helper: 3^49 does not divide 100! -/
lemma three_pow_49_not_dvd_factorial_100 : 
    ¬(3 ^ 49 ∣ Nat.factorial 100) := by norm_num

/-- Main theorem: h01_answer is the greatest k with 3^k dividing 100! -/
theorem h01_legendre100 :
    IsGreatest {k : ℕ | 3 ^ k ∣ Nat.factorial 100} h01_answer := by sorry
