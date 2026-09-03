import Mathlib

/-- Telescoping product: `∏_{k=2}^n (1 - 1/k²) = (n+1)/(2n)` for `n ≥ 2`. -/
theorem h05_telescope_prod (n : ℕ) (hn : 2 ≤ n) :
    ∏ k ∈ Finset.Icc 2 n, ((1 : ℝ) - 1 / (k : ℝ) ^ 2) = ((n : ℝ) + 1) / (2 * (n : ℝ)) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [Finset.Icc_self, Finset.prod_singleton]
  | succ n hn ih =>
    rw [Finset.prod_Icc_succ_top (by omega : 2 ≤ n + 1), ih]
    have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hn0 : (n : ℝ) ≠ 0 := by linarith
    have hn1 : (n : ℝ) + 1 ≠ 0 := by linarith
    push_cast
    field_simp
    ring
