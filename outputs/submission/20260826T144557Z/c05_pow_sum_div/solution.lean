import Mathlib

/-- `5` divides `2 ^ 2025 + 3 ^ 2025`. -/
theorem c05_pow_sum_div : 5 ∣ 2 ^ 2025 + 3 ^ 2025 := by
  have h₁ : 2 ^ 2025 % 5 = 2 := by
    rw [← Nat.mod_add_div (2025) 4]
    simp [pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
    <;> norm_num
    <;> omega
  
  have h₂ : 3 ^ 2025 % 5 = 3 := by
    rw [← Nat.mod_add_div (2025) 4]
    simp [pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
    <;> norm_num
    <;> omega
  
  have h₃ : (2 ^ 2025 + 3 ^ 2025) % 5 = 0 := by
    omega
  
  rw [Nat.dvd_iff_mod_eq_zero]
  exact h₃
