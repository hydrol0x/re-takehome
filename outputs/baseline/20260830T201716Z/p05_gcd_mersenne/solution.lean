import Mathlib

/-- What is the greatest common divisor of `2 ^ 1001 - 1` and `2 ^ 1012 - 1`?
Show that it is `2 ^ 11 - 1`. -/
theorem p05_gcd_mersenne : Nat.gcd (2 ^ 1001 - 1) (2 ^ 1012 - 1) = 2 ^ 11 - 1 := by
  have h1 : Nat.gcd 1001 1012 = 11 := by norm_num
  rw [← Nat.gcd_pow_sub_one]
  <;> simp [h1]
  <;> norm_num
