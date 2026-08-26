import Mathlib

set_option exponentiation.threshold 10000
set_option maxRecDepth 8000

/-- `5` divides `2 ^ 2025 + 3 ^ 2025`. -/
theorem c05_pow_sum_div : 5 ∣ 2 ^ 2025 + 3 ^ 2025 := by
  have h1 : (2 ^ 2025 + 3 ^ 2025) % 5 = 0 := by
    -- Note: 2025 = 4 * 506 + 1
    -- We use the fact that 2^4 ≡ 1 (mod 5) and 3^4 ≡ 1 (mod 5)
    rw [show 2025 = 4 * 506 + 1 by decide]
    rw [pow_add, pow_mul, pow_one]
    simp [Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
    <;> norm_num
    <;> rfl
  exact Nat.dvd_of_mod_eq_zero h1
