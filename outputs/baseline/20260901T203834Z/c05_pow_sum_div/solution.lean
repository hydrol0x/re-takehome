import Mathlib

/-- `5` divides `2 ^ 2025 + 3 ^ 2025`. -/
theorem c05_pow_sum_div : 5 ∣ 2 ^ 2025 + 3 ^ 2025 := by
  have h2 : (2 ^ 2025) % 5 = 2 := by
    norm_num
  have h3 : (3 ^ 2025) % 5 = 3 := by
    norm_num
  have hsum : (2 ^ 2025 + 3 ^ 2025) % 5 = 0 := by
    have : ((2 ^ 2025) % 5 + (3 ^ 2025) % 5) % 5 = 0 := by
      simpa [h2, h3] using (by norm_num : (2 + 3) % 5 = 0)
    simpa [Nat.add_mod, h2, h3] using this
  exact Nat.dvd_of_mod_eq_zero hsum
