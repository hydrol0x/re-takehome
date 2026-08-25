import Mathlib

/-- For k ≥ 2, we have 1/k² ≤ 1/(k-1) - 1/k -/
lemma invsq_le_telescoping (k : ℕ) (hk : 2 ≤ k) :
    (1 : ℝ) / (k : ℝ) ^ 2 ≤ (1 : ℝ) / ((k - 1 : ℕ) : ℝ) - (1 : ℝ) / (k : ℝ) := by sorry

/-- For n ≥ 1, ∑_{i=2}^n 1/i² ≤ 1 - 1/n -/
lemma invsq_sum_from_2 (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.Icc 2 n, (1 : ℝ) / (i : ℝ) ^ 2 ≤ (1 : ℝ) - (1 : ℝ) / (n : ℝ) := by sorry

/-- Main theorem: ∑_{i=1}^n 1/i² ≤ 2 - 1/n for n ≥ 1 -/
theorem h03_invsq_sum (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.Icc 1 n, (1 : ℝ) / (i : ℝ) ^ 2 ≤ 2 - 1 / (n : ℝ) := by sorry
