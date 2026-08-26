import Mathlib
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Real.Basic

/-- Telescoping product: `∏_{k=2}^n (1 - 1/k²) = (n+1)/(2n)` for `n ≥ 2`. -/
theorem h05_telescope_prod (n : ℕ) (hn : 2 ≤ n) :
    ∏ k ∈ Finset.Icc 2 n, ((1 : ℝ) - 1 / (k : ℝ) ^ 2) = ((n : ℝ) + 1) / (2 * (n : ℝ)) := by
  have h_main : ∀ m : ℕ, 2 ≤ m → ∏ k ∈ Finset.Icc 2 m, ((1 : ℝ) - 1 / (k : ℝ) ^ 2) = ((m : ℝ) + 1) / (2 * (m : ℝ)) := by
    intro m hm
    induction' hm with m hm IH
    · norm_num [Finset.prod_Icc_succ_top]
    cases m with
    | zero => contradiction
    | succ m' =>
      rw [Finset.prod_Icc_succ_top (by omega : 2 ≤ m'.succ + 1)]
      rw [IH]
      field_simp [Nat.cast_ne_zero]
      ring_nf
      <;> simp_all [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat]
      <;> field_simp [Nat.cast_ne_zero]
      <;> ring_nf
      <;> norm_num
      <;> linarith
  
  exact h_main n hn
