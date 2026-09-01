import Mathlib

/-- Helper: basic inequality k * (k + 2) ≤ (k + 1)^2 for all natural k -/
lemma h03_helper_poly_ineq (k : ℕ) :
    k * (k + 2) ≤ (k + 1) ^ 2 := by linarith

/-- Helper: if a*d ≤ b*c with positive reals, then c/b ≤ d/a -/
lemma h03_helper_frac_ineq (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a * d ≤ b * c) :
    c / b ≤ d / a := by sorry

/-- Helper: sum up to k+1 equals sum up to k plus the (k+1)-th term -/
lemma h03_helper_sum_add (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.Icc 1 (n + 1), (1 : ℝ) / (i : ℝ) ^ 2 = 
    (∑ i ∈ Finset.Icc 1 n, (1 : ℝ) / (i : ℝ) ^ 2) + (1 : ℝ) / ((n + 1) : ℝ) ^ 2 := by sorry

/-- Helper: (n+1)/((n+1)^2) = 1/(n+1) -/
lemma h03_helper_simple_frac (n : ℕ) (hn : 1 ≤ n) :
    (n + 1 : ℝ) / ((n + 1 : ℝ) ^ 2) = 1 / (n + 1 : ℝ) := by field_simp [pow_two]

/-- Main theorem with helper lemmas -/
theorem h03_invsq_sum (n : ℕ) (hn : 1 ≤ n) :
    ∑ i ∈ Finset.Icc 1 n, (1 : ℝ) / (i : ℝ) ^ 2 ≤ 2 - 1 / (n : ℝ) := by sorry
