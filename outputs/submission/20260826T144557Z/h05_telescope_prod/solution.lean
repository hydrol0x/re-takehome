import Mathlib

/-- Helper: Rewrite each term in the product as a fraction -/
lemma telescope_term_rewrite (k : ℕ) (hk : 2 ≤ k) :
    ((1 : ℝ) - 1 / (k : ℝ) ^ 2) = ((k - 1 : ℝ) * (k + 1 : ℝ)) / ((k : ℝ) ^ 2) := by calc
      (1 : ℝ) - 1 / (k : ℝ) ^ 2 = (k : ℝ) ^ 2 / (k : ℝ) ^ 2 - 1 / (k : ℝ) ^ 2 := by field_simp
      _ = ((k : ℝ) ^ 2 - 1) / (k : ℝ) ^ 2 := by field_simp
      _ = ((k - 1 : ℝ) * (k + 1 : ℝ)) / ((k : ℝ) ^ 2) := by ring

/-- Helper: Show that k ≠ 0 for k ≥ 2 -/
lemma ne_zero_of_ge_two (k : ℕ) (hk : 2 ≤ k) : (k : ℝ) ≠ 0 := by positivity

/-- Helper: The denominator 2 * k² is non-zero for k ≥ 2 -/
lemma denom_nonzero (k : ℕ) (hk : 2 ≤ k) : (2 : ℝ) * (k : ℝ) ^ 2 ≠ 0 := by positivity

/-- Main theorem: Telescoping product identity -/
theorem h05_telescope_prod (n : ℕ) (hn : 2 ≤ n) :
    ∏ k ∈ Finset.Icc 2 n, ((1 : ℝ) - 1 / (k : ℝ) ^ 2) = ((n : ℝ) + 1) / (2 * (n : ℝ)) := by sorry
