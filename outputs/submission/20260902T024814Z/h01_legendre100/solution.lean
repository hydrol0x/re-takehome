import Mathlib

/-- The largest `k` such that `3 ^ k ∣ 100!`. Must be a numeric literal. -/
abbrev h01_answer : ℕ := 48

/-- Compute Legendre's formula for the exponent of 3 in 100! -/
def legendre_3_in_100_factorial : ℕ :=
  100 / 3 + 100 / 9 + 100 / 27 + 100 / 81

lemma legendre_value : legendre_3_in_100_factorial = 48 := by
  rfl

/-- If 3^k divides n!, then k ≤ sum of floor(n/3^i) -/
lemma div_three_factorial_bound {n k : ℕ} (h : 3 ^ k ∣ Nat.factorial n) :
    k ≤ n / 3 + n / 9 + n / 27 + n / 81 + n / 243 := by sorry

/-- The specific bound for 100! -/
lemma div_three_100_factorial_bound {k : ℕ} (h : 3 ^ k ∣ Nat.factorial 100) :
    k ≤ 48 := by sorry

/-- 3^48 divides 100! -/
lemma three_48_dvd_100_factorial : 3 ^ 48 ∣ Nat.factorial 100 := by norm_num

/-- 3^49 does not divide 100! -/
lemma three_49_not_dvd_100_factorial : ¬(3 ^ 49 ∣ Nat.factorial 100) := by norm_num

/-- `h01_answer` is the greatest `k` with `3 ^ k` dividing `100!`. -/
theorem h01_legendre100 :
    IsGreatest {k : ℕ | 3 ^ k ∣ Nat.factorial 100} h01_answer := by sorry
