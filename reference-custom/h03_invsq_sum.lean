import Mathlib

/-- The classical bound `∑_{i=1}^n 1/i² ≤ 2 - 1/n` for `n ≥ 1`. -/
theorem h03_invsq_sum (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.Icc 1 n, (1 : ℝ) / (i : ℝ) ^ 2 ≤ 2 - 1 / (n : ℝ) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [Finset.Icc_self, Finset.sum_singleton]
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]
    have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
    have h01 : (n : ℝ) ≠ 0 := ne_of_gt hn0
    have h02 : (n : ℝ) + 1 ≠ 0 := ne_of_gt hn1
    have hdiff : (1 : ℝ) / (n : ℝ) - 1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 1) ^ 2
        = 1 / ((n : ℝ) * ((n : ℝ) + 1) ^ 2) := by
      field_simp
      ring
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) * ((n : ℝ) + 1) ^ 2) := by
      apply div_pos one_pos
      nlinarith
    have key : (1 : ℝ) / ((n : ℝ) + 1) ^ 2 ≤ 1 / (n : ℝ) - 1 / ((n : ℝ) + 1) := by
      nlinarith [hdiff, hpos]
    push_cast
    linarith [ih, key]
