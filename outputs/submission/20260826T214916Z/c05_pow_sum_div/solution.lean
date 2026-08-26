import Mathlib

/-- `5` divides `2 ^ 2025 + 3 ^ 2025`. -/
theorem c05_pow_sum_div : 5 ∣ 2 ^ 2025 + 3 ^ 2025 := by
  rw [Nat.dvd_iff_mod_eq_zero]
  have h₁ : (2 ^ 2025 + 3 ^ 2025) % 5 = 0 := by
    have h₂ : 2025 % 4 = 1 := by norm_num
    have h₃ : 2 ^ 2025 % 5 = 2 ^ (2025 % 4) % 5 := by
      rw [← Nat.mod_add_div 2025 4]
      simp [pow_add, pow_mul, Nat.pow_mod]
      <;> norm_num
      <;> omega
    have h₄ : 3 ^ 2025 % 5 = 3 ^ (2025 % 4) % 5 := by
      rw [← Nat.mod_add_div 2025 4]
      simp [pow_add, pow_mul, Nat.pow_mod]
      <;> norm_num
      <;> omega
    calc
      (2 ^ 2025 + 3 ^ 2025) % 5 = (2 ^ 2025 % 5 + 3 ^ 2025 % 5) % 5 := by
        simp [Nat.add_mod]
      _ = (2 ^ (2025 % 4) % 5 + 3 ^ (2025 % 4) % 5) % 5 := by rw [h₃, h₄]
      _ = (2 ^ 1 % 5 + 3 ^ 1 % 5) % 5 := by rw [h₂]
      _ = (2 + 3) % 5 := by norm_num
      _ = 5 % 5 := by norm_num
      _ = 0 := by norm_num
  exact h₁
