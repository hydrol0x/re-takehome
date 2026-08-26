import Mathlib

set_option exponentiation.threshold 10000
set_option maxRecDepth 8000

/-- `5` divides `2 ^ 2025 + 3 ^ 2025`. -/
theorem c05_pow_sum_div : 5 ∣ 2 ^ 2025 + 3 ^ 2025 := by
  norm_num [Nat.dvd_iff_mod_eq_zero]
  <;> simp [pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
  <;> rfl
