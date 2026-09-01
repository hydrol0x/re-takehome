import Mathlib

/-- The classical bound `∑_{i=1}^n 1/i² ≤ 2 - 1/n` for `n ≥ 1`. -/
theorem h03_invsq_sum (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.Icc 1 n, (1 : ℝ) / (i : ℝ) ^ 2 ≤ 2 - 1 / (n : ℝ) := by
  -- write `n = k.succ`
  rcases Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt (lt_of_lt_of_le (Nat.succ_pos 0) hn)) with ⟨k, rfl⟩
  -- now the goal is for `k.succ`
  induction k with
  | zero =>
      -- base case `n = 1`
      simp
  | succ k ih =>
      -- use the telescoping decomposition of the sum
      have hsum :
          ∑ i ∈ Finset.Icc 1 (k + 2), (1 : ℝ) / (i : ℝ) ^ 2 =
            (∑ i ∈ Finset.Icc 1 (k + 1), (1 : ℝ) / (i : ℝ) ^ 2) +
              (1 : ℝ) / ((k + 2) : ℝ) ^ 2 := by
        have hle : (1 : ℕ) ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
        simpa using
          (Finset.sum_Icc_succ_top
            (f := fun i : ℕ => (1 : ℝ) / (i : ℝ) ^ 2) hle)
      have htemp :
          (∑ i ∈ Finset.Icc 1 (k + 2), (1 : ℝ) / (i : ℝ) ^ 2) ≤
            (2 - 1 / ((k + 1) : ℝ)) + (1 : ℝ) / ((k + 2) : ℝ) ^ 2 := by
        simpa [hsum] using add_le_add_right ih _
      have hfinal :
          (2 - 1 / ((k + 1) : ℝ)) + (1 : ℝ) / ((k + 2) : ℝ) ^ 2 ≤
            2 - 1 / ((k + 2) : ℝ) := by
        have hpos1 : (0 : ℝ) < (k + 1 : ℝ) := by
          exact_mod_cast (Nat.succ_pos _)
        have hpos2 : (0 : ℝ) < (k + 2 : ℝ) := by
          exact_mod_cast (Nat.succ_pos _)
        nlinarith
      exact le_trans htemp hfinal
