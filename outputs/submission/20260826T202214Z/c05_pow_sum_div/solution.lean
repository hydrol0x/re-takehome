import Mathlib

/-- `5` divides `2 ^ 2025 + 3 ^ 2025`. -/
theorem c05_pow_sum_div : 5 ∣ 2 ^ 2025 + 3 ^ 2025 := by
  rw [Nat.dvd_iff_mod_eq_zero]
  
  -- Compute 2^2025 mod 5 using the fact that 2^4 ≡ 1 (mod 5)
  have h₁ : (2 ^ 2025) % 5 = 2 := by
    rw [show 2025 = 4 * 506 + 1 by decide]
    rw [pow_add, pow_mul]
    simp [Nat.pow_mod, Nat.mul_mod, Nat.mod_mod]
    <;> norm_num
  
  -- Compute 3^2025 mod 5 using the fact that 3^4 ≡ 1 (mod 5)
  have h₂ : (3 ^ 2025) % 5 = 3 := by
    rw [show 2025 = 4 * 506 + 1 by decide]
    rw [pow_add, pow_mul]
    simp [Nat.pow_mod, Nat.mul_mod, Nat.mod_mod]
    <;> norm_num
  
  -- Show the sum is 0 mod 5
  simp [h₁, h₂, Nat.add_mod]
  <;> norm_num
