import Mathlib

/-- Helper: Algebraic decomposition of the product term. -/
lemma prod_term_decomp (k : ℕ) (hk : 2 ≤ k) :
    ((1 : ℝ) - 1 / (k : ℝ) ^ 2) = ((k : ℝ) - 1) * ((k : ℝ) + 1) / ((k : ℝ) ^ 2) := by
  field_simp [pow_two]
  ring

/-- Helper: Product up to n equals partial fraction form. -/
lemma prod_partial_fraction (n : ℕ) (hn : 2 ≤ n) :
    ∏ k ∈ Finset.Icc 2 n, ((k : ℝ) - 1) * ((k : ℝ) + 1) / ((k : ℝ) ^ 2) = 
    ((n : ℝ) + 1) / (2 * (n : ℝ)) := by
  sorry

/-- Main proof using helper lemmas. -/
theorem h05_telescope_prod (n : ℕ) (hn : 2 ≤ n) :
    ∏ k ∈ Finset.Icc 2 n, ((1 : ℝ) - 1 / (k : ℝ) ^ 2) = ((n : ℝ) + 1) / (2 * (n : ℝ)) := by
  rw [Finset.prod_congr rfl fun k hk => prod_term_decomp k (Finset.mem_Icc.mp hk).1]
  exact prod_partial_fraction n hn
