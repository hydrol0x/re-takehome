import Mathlib

/-- Simplifies each term in the telescoping product. -/
lemma term_simplification (k : ℕ) (hk : 2 ≤ k) : 
    ((1 : ℝ) - 1 / (k : ℝ) ^ 2) = ((k - 1 : ℝ) * (k + 1 : ℝ)) / ((k : ℝ) ^ 2) := by
  have h1 : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.cast_ne_zero.mpr (Nat.ne_of_gt (by linarith))
  field_simp [h1]
  ring
  <;> norm_num
  <;> linarith

/-- Helper for the telescoping pattern: numerator accumulates as k+1. -/
lemma prod_pattern (n : ℕ) (hn : 2 ≤ n) :
    ∏ k ∈ Finset.Icc 2 n, ((k - 1 : ℝ) * (k + 1 : ℝ)) / ((k : ℝ) ^ 2) =
      ((n : ℝ) + 1) / (2 * (n : ℝ)) := by sorry

/-- Main theorem using helper lemmas. -/
theorem h05_telescope_prod (n : ℕ) (hn : 2 ≤ n) :
    ∏ k ∈ Finset.Icc 2 n, ((1 : ℝ) - 1 / (k : ℝ) ^ 2) = ((n : ℝ) + 1) / (2 * (n : ℝ)) := by
  rw [Finset.prod_congr rfl fun k hk => term_simplification k (Finset.mem_Icc.mp hk).1]
  exact prod_pattern n hn
