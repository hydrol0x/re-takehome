import Mathlib

/-- The classical bound `∑_{i=1}^n 1/i² ≤ 2 - 1/n` for `n ≥ 1`. -/
theorem h03_invsq_sum (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.Icc 1 n, (1 : ℝ) / (i : ℝ) ^ 2 ≤ 2 - 1 / (n : ℝ) := by
  sorry
