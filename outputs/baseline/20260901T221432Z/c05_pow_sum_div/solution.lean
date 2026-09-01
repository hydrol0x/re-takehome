import Mathlib

/-- `5` divides `2 ^ 2025 + 3 ^ 2025`. -/
theorem c05_pow_sum_div : 5 ∣ 2 ^ 2025 + 3 ^ 2025 := by
  have h : (2 ^ 2025 + 3 ^ 2025) % 5 = 0 := by
    norm_num
  exact Nat.dvd_of_mod_eq_zero h
