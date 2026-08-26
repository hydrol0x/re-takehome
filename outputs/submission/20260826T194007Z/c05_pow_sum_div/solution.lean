import Mathlib

set_option exponentiation.threshold 10000
set_option maxRecDepth 8000

/-- `5` divides `2 ^ 2025 + 3 ^ 2025`. -/
theorem c05_pow_sum_div : 5 ∣ 2 ^ 2025 + 3 ^ 2025 := by
  apply Nat.dvd_of_mod_eq_zero
  rw [← Nat.mod_add_div (2 ^ 2025 + 3 ^ 2025) 5]
  simp [Nat.add_mod, Nat.pow_mod, Nat.mul_mod]
  <;> decide
