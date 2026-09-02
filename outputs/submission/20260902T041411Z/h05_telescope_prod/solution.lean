import Mathlib

/-- Telescoping product: `∏_{k=2}^n (1 - 1/k²) = (n+1)/(2n)` for `n ≥ 2`. -/
theorem h05_telescope_prod (n : ℕ) (hn : 2 ≤ n) :
    ∏ k ∈ Finset.Icc 2 n, ((1 : ℝ) - 1 / (k : ℝ) ^ 2) = ((n : ℝ) + 1) / (2 * (n : ℝ)) := by
  have h : ∀ n : ℕ, 2 ≤ n → ∏ k ∈ Finset.Icc 2 n, ((1 : ℝ) - 1 / (k : ℝ) ^ 2) = ((n : ℝ) + 1) / (2 * (n : ℝ)) := by
    intro n hn
    induction' hn with n hn IH
    · -- Base case: n = 2
      norm_num [Finset.prod_Icc_succ_top]
    · -- Inductive step
      cases n with
      | zero => contradiction  -- Can't happen since 2 ≤ n
      | succ n =>
        simp_all [Finset.prod_Icc_succ_top, Nat.cast_add, Nat.cast_one, Nat.cast_mul, 
                  add_mul, mul_add, mul_one, div_eq_mul_inv]
        field_simp at *
        ring_nf at *
        <;>
        (try omega) <;>
        (try norm_num at *) <;>
        (try linarith) <;>
        (try {
          cases n with
          | zero => contradiction
          | succ n =>
            field_simp
            ring_nf
            <;> norm_num
            <;> linarith
        })
        <;>
        (try {
          simp_all [Nat.succ_eq_add_one]
          field_simp
          ring_nf
          <;> norm_num
          <;> linarith
        })
  exact h n hn
