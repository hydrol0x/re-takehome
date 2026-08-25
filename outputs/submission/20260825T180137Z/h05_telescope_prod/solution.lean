import Mathlib

/-- Telescoping product: `∏_{k=2}^n (1 - 1/k²) = (n+1)/(2n)` for `n ≥ 2`. -/
theorem h05_telescope_prod (n : ℕ) (hn : 2 ≤ n) :
    ∏ k ∈ Finset.Icc 2 n, ((1 : ℝ) - 1 / (k : ℝ) ^ 2) = ((n : ℝ) + 1) / (2 * (n : ℝ)) := by
  have h_main : ∀ (n : ℕ), 2 ≤ n → ∏ k ∈ Finset.Icc 2 n, ((1 : ℝ) - 1 / (k : ℝ) ^ 2) = ((n : ℝ) + 1) / (2 * (n : ℝ)) := by
    intro n hn
    induction' hn with n hn IH
    · norm_num [Finset.prod_Icc_succ_top]
    · cases n with
      | zero => contradiction
      | succ n =>
        rw [Finset.prod_Icc_succ_top (by omega : 2 ≤ n.succ + 1)]
        rw [IH]
        field_simp
        ring_nf
        <;> simp_all [Nat.cast_add, Nat.cast_one]
        <;> field_simp
        <;> ring_nf
        <;> norm_num
        <;> linarith
  
  apply h_main
  exact hn
