import Mathlib

/-- For i ≥ 2, we have 1/i² ≤ 1/(i-1) - 1/i -/
lemma inv_sq_le_diff (i : ℕ) (hi : 2 ≤ i) : 
    (1 : ℝ) / (i : ℝ) ^ 2 ≤ (1 : ℝ) / ((i - 1 : ℕ) : ℝ) - (1 : ℝ) / (i : ℝ) := by sorry

/-- The telescoping sum ∑_{i=2}^{n} (1/(i-1) - 1/i) equals 1 - 1/n -/
lemma sum_telescoping (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.Icc 2 n, ((1 : ℝ) / ((i - 1 : ℕ) : ℝ) - (1 : ℝ) / (i : ℝ)) = 1 - 1 / (n : ℝ) := by sorry

/-- Split the sum at i=1 -/
lemma sum_split_1 (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.Icc 1 n, (1 : ℝ) / (i : ℝ) ^ 2 = (1 : ℝ) + ∑ i ∈ Finset.Icc 2 n, (1 : ℝ) / (i : ℝ) ^ 2 := by sorry

/-- Main theorem: ∑_{i=1}^n 1/i² ≤ 2 - 1/n for n ≥ 1 -/
theorem h03_invsq_sum (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.Icc 1 n, (1 : ℝ) / (i : ℝ) ^ 2 ≤ 2 - 1 / (n : ℝ) := by sorry
