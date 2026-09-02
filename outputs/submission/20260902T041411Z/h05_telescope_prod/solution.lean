import Mathlib

/-- Telescoping product: `∏_{k=2}^n (1 - 1/k²) = (n+1)/(2n)` for `n ≥ 2`. -/
theorem h05_telescope_prod (n : ℕ) (hn : 2 ≤ n) :
    ∏ k ∈ Finset.Icc 2 n, ((1 : ℝ) - 1 / (k : ℝ) ^ 2) = ((n : ℝ) + 1) / (2 * (n : ℝ)) := by
  have h_main : ∀ (n : ℕ), 2 ≤ n → ∏ k ∈ Finset.Icc 2 n, ((1 : ℝ) - 1 / (k : ℝ) ^ 2) = ((n : ℝ) + 1) / (2 * (n : ℝ)) := by
    intro n hn
    induction' hn with n ih IH
    · norm_num [Finset.prod_Icc_succ_top]
    · cases n with
      | zero => contradiction
      | succ n =>
        rw [Finset.prod_Icc_succ_top (by omega)]
        rw [IH]
        simp [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_two]
        field_simp
        ring
        <;> field_simp
        <;> ring
        <;> norm_cast
        <;> field_simp
        <;> ring
  
  exact h_main n hn
