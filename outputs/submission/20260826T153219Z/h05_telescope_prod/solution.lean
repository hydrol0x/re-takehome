import Mathlib

/-- Telescoping product: `∏_{k=2}^n (1 - 1/k²) = (n+1)/(2n)` for `n ≥ 2`. -/
theorem h05_telescope_prod (n : ℕ) (hn : 2 ≤ n) :
    ∏ k ∈ Finset.Icc 2 n, ((1 : ℝ) - 1 / (k : ℝ) ^ 2) = ((n : ℝ) + 1) / (2 * (n : ℝ)) := by
  have h_main : ∀ m : ℕ, 2 ≤ m → ∏ k ∈ Finset.Icc 2 m, ((1 : ℝ) - 1 / (k : ℝ) ^ 2) = ((m : ℝ) + 1) / (2 * (m : ℝ)) := by
    intro m hm
    induction' hm with m hm IH
    · -- Base case: m = 2
      norm_num [Finset.prod_Icc_succ_top]
    · -- Inductive step: assume true for m, prove for m + 1
      cases m with
      | zero => contradiction  -- Cannot happen since 2 ≤ m
      | succ m =>
        simp_all [Finset.prod_Icc_succ_top, Nat.cast_add, Nat.cast_one, mul_add, add_mul]
        field_simp at *
        ring_nf at *
        <;>
        (try norm_cast) <;>
        (try simp_all) <;>
        (try field_simp at *) <;>
        (try ring_nf at *) <;>
        (try norm_num at *) <;>
        (try linarith)
        <;>
        (try
          {
            rw [← sub_eq_zero]
            ring_nf
            <;> field_simp at *
            <;> norm_cast at *
            <;> ring_nf at *
          })
        <;>
        (try
          {
            apply eq_of_sub_eq_zero
            field_simp at *
            <;> ring_nf at *
            <;> norm_cast at *
            <;> linarith
          })
  
  exact h_main n hn
