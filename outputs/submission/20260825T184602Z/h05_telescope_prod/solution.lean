import Mathlib

/-- Telescoping product: `∏_{k=2}^n (1 - 1/k²) = (n+1)/(2n)` for `n ≥ 2`. -/
theorem h05_telescope_prod (n : ℕ) (hn : 2 ≤ n) :
    ∏ k ∈ Finset.Icc 2 n, ((1 : ℝ) - 1 / (k : ℝ) ^ 2) = ((n : ℝ) + 1) / (2 * (n : ℝ)) := by
  have h_main : ∀ m : ℕ, m ≥ 2 → ∏ k ∈ Finset.Icc 2 m, ((1 : ℝ) - 1 / (k : ℝ) ^ 2) = ((m : ℝ) + 1) / (2 * (m : ℝ)) := by
    intro m hm
    induction' hm with m hm IH
    · -- Base case: m = 2
      norm_num [Finset.prod_Icc_succ_top]
    · -- Inductive step: assume true for m, prove for m + 1
      cases m with
      | zero => contradiction -- Can't happen since m ≥ 2
      | succ m' =>
        rw [Finset.prod_Icc_succ_top (by omega)]
        rw [IH]
        simp [Nat.cast_add, Nat.cast_one, add_assoc]
        field_simp
        ring_nf
        <;> norm_cast
        <;> ring_nf at *
        <;> field_simp at *
        <;> norm_num
        <;> linarith
  exact h_main n hn
