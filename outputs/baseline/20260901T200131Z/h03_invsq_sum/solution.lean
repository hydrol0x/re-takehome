import Mathlib

/-- The classical bound `∑_{i=1}^n 1/i² ≤ 2 - 1/n` for `n ≥ 1`. -/
theorem h03_invsq_sum (n : ℕ) (hn : 1 ≤ n) :
    ∑ i in Finset.Icc 1 n, (1 : ℝ) / (i : ℝ) ^ 2 ≤ 2 - 1 / (n : ℝ) := by
  have h_main : ∀ k : ℕ, 1 ≤ k → ∑ i in Finset.Icc 1 k, (1 : ℝ) / (i : ℝ) ^ 2 ≤ 2 - 1 / (k : ℝ) := by
    intro k hk
    induction' hk with k hk IH
    · norm_num [Finset.sum_Icc_succ_top]
    · cases k with
      | zero => contradiction
      | succ k' =>
        simp_all [Finset.sum_Icc_succ_top, Nat.cast_add, Nat.cast_one, add_assoc]
        rw [← sub_nonneg]
        field_simp
        ring_nf
        positivity
  exact h_main n hn
