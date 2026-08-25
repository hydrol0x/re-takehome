import Mathlib

/-- The largest `k` such that `3 ^ k ∣ 100!`. Must be a numeric literal. -/
abbrev h01_answer : ℕ := 48

/-- Helper: Compute v_3(100!) using Legendre's formula. -/
lemma legendre_v3_100 : 
    (Nat.factorial 100).factorization 3 = 48 := by sorry

/-- Helper: Show that 3^48 divides 100!. -/
lemma leg_divides_100_fact : 3 ^ 48 ∣ Nat.factorial 100 := by norm_num

/-- Helper: Show that 3^49 does NOT divide 100!. -/
lemma leg_not_divides_100_fact : ¬(3 ^ 49 ∣ Nat.factorial 100) := by norm_num

/-- Main theorem: h01_answer is the greatest k with 3^k dividing 100!. -/
theorem h01_legendre100 :
    IsGreatest {k : ℕ | 3 ^ k ∣ Nat.factorial 100} h01_answer := by sorry
