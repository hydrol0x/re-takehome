import Mathlib

/-- The classical bound `∑_{i=1}^n 1/i² ≤ 2 - 1/n` for `n ≥ 1`. -/
theorem h03_invsq_sum (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.Icc 1 n, (1 : ℝ) / (i : ℝ) ^ 2 ≤ 2 - 1 / (n : ℝ) := by
  -- auxiliary inequality: `1/(k+1)² ≤ 1/k - 1/(k+1)` for `k ≥ 1`
  have h_ineq (k : ℕ) (hk : 1 ≤ k) :
      (1 : ℝ) / ((k + 1 : ℝ) ^ 2) ≤ (1 : ℝ) / (k : ℝ) - (1 : ℝ) / ((k + 1 : ℝ)) := by
    have hk0 : (0 : ℝ) < (k : ℝ) := by
      have : (0 : ℕ) < k := Nat.lt_of_lt_of_le (Nat.succ_pos _) hk
      exact_mod_cast this
    have hk1 : (0 : ℝ) < (k + 1 : ℝ) := by
      exact_mod_cast (Nat.succ_pos _)
    have hle : (k : ℝ) * (k + 1 : ℝ) ≤ (k + 1 : ℝ) ^ 2 := by
      have : (k : ℝ) ≤ (k + 1 : ℝ) := by
        exact_mod_cast (Nat.le_succ _)
      have := mul_le_mul_of_nonneg_right this (le_of_lt hk1)
      simpa [pow_two] using this
    have h1 :
        (1 : ℝ) / ((k + 1 : ℝ) ^ 2) ≤ (1 : ℝ) / ((k : ℝ) * (k + 1 : ℝ)) := by
      have hpos1 : (0 : ℝ) < ((k + 1 : ℝ) ^ 2) := by
        have : (0 : ℝ) < (k + 1 : ℝ) := hk1
        simpa [pow_two] using mul_pos this this
      have hpos2 : (0 : ℝ) < (k : ℝ) * (k + 1 : ℝ) := mul_pos hk0 hk1
      exact (one_div_le_one_div_iff hpos2 hpos1).mpr hle
    have h2 :
        (1 : ℝ) / ((k : ℝ) * (k + 1 : ℝ)) =
          (1 : ℝ) / (k : ℝ) - (1 : ℝ) / ((k + 1 : ℝ)) := by
      field_simp [pow_two, mul_comm, mul_left_comm, mul_assoc]
    simpa [h2] using h1

  -- prove the statement by induction on `n` (after eliminating the impossible case `n = 0`)
  cases n with
  | zero =>
      exact (Nat.not_succ_le_self 0 hn).elim
  | succ n' =>
      -- we now have `n = n' + 1` and `hn : 1 ≤ n' + 1`
      have : 1 ≤ n' + 1 := hn
      clear hn
      -- induction on `n'`
      induction n' with
      | zero =>
          -- case `n = 1`
          simp
      | succ n'' ih =>
          -- now `n = n'' + 2`
          have hsum_eq :
              ∑ i ∈ Finset.Icc 1 (n'' + 2), (1 : ℝ) / (i : ℝ) ^ 2 =
                (∑ i ∈ Finset.Icc 1 (n'' + 1), (1 : ℝ) / (i : ℝ) ^ 2) +
                  (1 : ℝ) / ((n'' + 2 : ℝ) ^ 2) := by
            simpa [
