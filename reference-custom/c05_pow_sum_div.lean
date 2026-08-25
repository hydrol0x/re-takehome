import Mathlib

/-- `5` divides `2 ^ 2025 + 3 ^ 2025`. -/
theorem c05_pow_sum_div : 5 ∣ 2 ^ 2025 + 3 ^ 2025 := by
  have h2 : (2 : ℕ) ^ 2025 % 5 = 2 := by
    conv_lhs => rw [show 2025 = 4 * 506 + 1 from rfl]
    rw [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  have h3 : (3 : ℕ) ^ 2025 % 5 = 3 := by
    conv_lhs => rw [show 2025 = 4 * 506 + 1 from rfl]
    rw [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  omega
