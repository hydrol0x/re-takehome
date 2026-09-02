import Mathlib

/-- For i ≥ 2, we have 1/i² ≤ 1/(i(i-1)). -/
lemma inv_sq_bound_helper (i : ℕ) (hi : 2 ≤ i) :
    (1 : ℝ) / (i : ℝ) ^ 2 ≤ (1 : ℝ) / ((i : ℝ) * ((i : ℝ) - 1)) := by
  sorry

/-- Decomposition of 1/(i(i-1)) as difference of reciprocals. -/
lemma inv_prod_decomp (i : ℕ) (hi : 2 ≤ i) :
    (1 : ℝ) / ((i : ℝ) * ((i : ℝ) - 1)) = (1 : ℝ) / ((i : ℝ) - 1) - (1 : ℝ) / (i : ℝ) := by
  have h₁ : (i : ℝ) - 1 ≠ 0 := by
    have : (i : ℝ) ≥ 2 := by exact_mod_cast hi
    linarith
  have h₂ : (i : ℝ) ≠ 0 := by
    have : (i : ℝ) ≥ 2 := by exact_mod_cast hi
    linarith
  field_simp [h₁, h₂]
  ring

/-- Partial sum bound from index 2 to n. -/
lemma partial_sum_bound (n : ℕ) (hn : 2 ≤ n) :
    ∑ i ∈ Finset.Icc 2 n, (1 : ℝ) / (i : ℝ) ^ 2 ≤ 1 - 1 / (n : ℝ) := by
  sorry

/-- Main theorem: classical bound for inverse square sum. -/
theorem h03_invsq_sum (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.Icc 1 n, (1 : ℝ) / (i : ℝ) ^ 2 ≤ 2 - 1 / (n : ℝ) := by
  sorry
