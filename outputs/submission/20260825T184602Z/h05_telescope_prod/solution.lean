import Mathlib

/-- Helper lemma: ∏_{k=2}^n (k-1)/k = 1/n for n ≥ 2 -/
lemma prod_frac_decreasing (n : ℕ) (hn : 2 ≤ n) :
    ∏ k ∈ Finset.Icc 2 n, ((k : ℝ) - 1) / (k : ℝ) = 1 / (n : ℝ) := by sorry

/-- Helper lemma: ∏_{k=2}^n (k+1)/k = (n+1)/2 for n ≥ 2 -/
lemma prod_frac_increasing (n : ℕ) (hn : 2 ≤ n) :
    ∏ k ∈ Finset.Icc 2 n, ((k : ℝ) + 1) / (k : ℝ) = ((n : ℝ) + 1) / 2 := by sorry

/-- Helper lemma: 1 - 1/k² = (k-1)(k+1)/k² for any positive real k -/
lemma one_minus_inv_sq (k : ℝ) (hk : k ≠ 0) :
    (1 : ℝ) - 1 / k ^ 2 = ((k - 1) * (k + 1)) / k ^ 2 := by calc
      (1 : ℝ) - 1 / k ^ 2 = k ^ 2 / k ^ 2 - 1 / k ^ 2 := by field_simp [hk]
      _ = (k ^ 2 - 1) / k ^ 2 := by rw [← sub_div]
      _ = ((k - 1) * (k + 1)) / k ^ 2 := by 
        have h : k ^ 2 - 1 = (k - 1) * (k + 1) := by ring
        rw [h]

/-- Main theorem: Telescoping product identity -/
theorem h05_telescope_prod (n : ℕ) (hn : 2 ≤ n) :
    ∏ k ∈ Finset.Icc 2 n, ((1 : ℝ) - 1 / (k : ℝ) ^ 2) = ((n : ℝ) + 1) / (2 * (n : ℝ)) := by sorry
