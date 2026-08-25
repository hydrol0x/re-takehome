import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Tactic.Ring

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
      | zero => contradiction -- Cannot happen since 2 ≤ m
      | succ m =>
        simp_all [Finset.prod_Icc_succ_top, Nat.cast_add, Nat.cast_one, Nat.cast_mul]
        field_simp
        ring_nf
        <;>
        (try norm_num) <;>
        (try linarith) <;>
        (try simp_all [Finset.prod_Icc_succ_top])
  exact h_main n hn
