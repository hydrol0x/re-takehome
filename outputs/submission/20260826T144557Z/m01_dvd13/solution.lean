import Mathlib

/-- For every natural number `n`, `13` divides `4 ^ (2 * n + 1) + 3 ^ (n + 2)`. -/
theorem m01_dvd13 (n : ℕ) : 13 ∣ 4 ^ (2 * n + 1) + 3 ^ (n + 2) := by
  have h_base : 13 ∣ 4 ^ (2 * 0 + 1) + 3 ^ (0 + 2) := by norm_num
  have h_ind_step : ∀ k : ℕ, 13 ∣ 4 ^ (2 * k + 1) + 3 ^ (k + 2) → 13 ∣ 4 ^ (2 * (k + 1) + 1) + 3 ^ ((k + 1) + 2) := by sorry
  have h_main : ∀ n : ℕ, 13 ∣ 4 ^ (2 * n + 1) + 3 ^ (n + 2) := by sorry
  exact h_main n
