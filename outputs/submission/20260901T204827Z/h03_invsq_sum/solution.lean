import Mathlib

/-- Lemma: For `k ≥ 2`, `1/k² ≤ 1/(k-1) - 1/k`. -/
lemma inv_sq_le_diff (k : ℕ) (hk : 2 ≤ k) :
    (1 : ℝ) / (k : ℝ) ^ 2 ≤ (1 : ℝ) / ((k : ℝ) - 1) - (1 : ℝ) / (k : ℝ) := by sorry

/-- Lemma: Sum of `1/(i-1) - 1/i` from `i=2` to `n` is `1 - 1/n`. -/
lemma sum_telescoping (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.Icc 2 n, ((1 : ℝ) / ((i : ℝ) - 1) - (1 : ℝ) / (i : ℝ)) = (1 : ℝ) - 1 / (n : ℝ) := by sorry

/-- Lemma: Split the sum at `1`. -/
lemma sum_split_1 (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.Icc 1 n, (1 : ℝ) / (i : ℝ) ^ 2 = (1 : ℝ) + ∑ i ∈ Finset.Icc 2 n, (1 : ℝ) / (i : ℝ) ^ 2 := by sorry

set_option maxHeartbeats 1000000
set_option exponentiation.threshold 10000
set_option maxRecDepth 8000

/-- The classical bound `∑_{i=1}^n 1/i² ≤ 2 - 1/n` for `n ≥ 1`. -/
theorem h03_invsq_sum (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.Icc 1 n, (1 : ℝ) / (i : ℝ) ^ 2 ≤ 2 - 1 / (n : ℝ) := by sorry
