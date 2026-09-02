import Mathlib

/-- For k ≥ 1, the contribution of the (k+1)-th term is bounded by the difference 1/k - 1/(k+1). -/
lemma inv_sq_step (k : ℕ) (hk : 1 ≤ k) :
    (1 : ℝ) / (k + 1 : ℝ) ^ 2 ≤ (1 : ℝ) / (k : ℝ) - (1 : ℝ) / (k + 1 : ℝ) := by sorry

/-- Decomposes the sum over Icc 1 (k+1) into the sum over Icc 1 k plus the last term. -/
lemma sum_Icc_succ_decomp (k : ℕ) (hk : 1 ≤ k) :
    ∑ i ∈ Finset.Icc 1 (k + 1), (1 : ℝ) / (i : ℝ) ^ 2 = 
    ∑ i ∈ Finset.Icc 1 k, (1 : ℝ) / (i : ℝ) ^ 2 + (1 : ℝ) / (k + 1 : ℝ) ^ 2 := by sorry

/-- The classical bound `∑_{i=1}^n 1/i² ≤ 2 - 1/n` for `n ≥ 1`. -/
theorem h03_invsq_sum (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.Icc 1 n, (1 : ℝ) / (i : ℝ) ^ 2 ≤ 2 - 1 / (n : ℝ) := by sorry
