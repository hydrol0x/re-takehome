import Mathlib

/-- Telescoping product: `∏_{k=2}^n (1 - 1/k²) = (n+1)/(2n)` for `n ≥ 2`. -/
theorem h05_telescope_prod (n : ℕ) (hn : 2 ≤ n) :
    ∏ k ∈ Finset.Icc 2 n, ((1 : ℝ) - 1 / (k : ℝ) ^ 2) = ((n : ℝ) + 1) / (2 * (n : ℝ)) := by
  have h_main : ∀ (m : ℕ), m ≥ 2 → ∏ k ∈ Finset.Icc 2 m, ((1 : ℝ) - 1 / (k : ℝ) ^ 2) = ((m : ℝ) + 1) / (2 * (m : ℝ)) := by sorry
  exact h_main n hn
