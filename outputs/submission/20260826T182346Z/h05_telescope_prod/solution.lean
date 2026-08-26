import Mathlib

/-- Telescoping product: `∏_{k=2}^n (1 - 1/k²) = (n+1)/(2n)` for `n ≥ 2`. -/
theorem h05_telescope_prod (n : ℕ) (hn : 2 ≤ n) :
    ∏ k ∈ Finset.Icc 2 n, ((1 : ℝ) - 1 / (k : ℝ) ^ 2) = ((n : ℝ) + 1) / (2 * (n : ℝ)) := by
  have h_main : ∀ n : ℕ, 2 ≤ n → ∏ k ∈ Finset.Icc 2 n, ((1 : ℝ) - 1 / (k : ℝ) ^ 2) = ((n : ℝ) + 1) / (2 * (n : ℝ)) := by
    intro n hn
    induction' hn with n hn IH
    · -- Base case: n = 2
      norm_num [Finset.prod_Icc_succ_top]
    · -- Inductive step
      cases n with
      | zero => contradiction
      | succ n =>
        rw [Finset.prod_Icc_succ_top (by omega : 2 ≤ n.succ + 1)]
        rw [IH]
        simp [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_two]
        field_simp
        ring_nf
        <;> field_simp [Nat.cast_ne_zero.mpr (show n.succ ≠ 0 by omega)]
        <;> ring_nf
        <;> field_simp [Nat.cast_ne_zero.mpr (show n.succ ≠ 0 by omega)]
        <;> norm_cast
        <;> ring_nf
        <;> field_simp [Nat.cast_ne_zero.mpr (show n.succ ≠ 0 by omega)]
        <;> linarith
  
  exact h_main n hn
