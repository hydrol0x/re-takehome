import Mathlib

/-- For positive reals with sum 1, their product is at most 1/4. -/
lemma prod_le_one_quarter (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hsum : x + y = 1) :
    x * y ≤ 1 / 4 := by
  nlinarith [sq_nonneg (x - y)]

/-- Expanding (1 + 1/x)(1 + 1/y) gives 1 + 2/(xy) when x + y = 1. -/
lemma expand_product (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (hsum : x + y = 1) :
    (1 + 1 / x) * (1 + 1 / y) = 1 + 2 / (x * y) := by
  try push_cast
  try field_simp
  try ring_nf
  nlinarith

/-- If 0 < p and p ≤ 1/4, then 2/p ≥ 8. -/
lemma two_div_bound (p : ℝ) (hp_pos : 0 < p) (hp_le : p ≤ 1 / 4) :
    2 / p ≥ 8 := by
  try push_cast
  try field_simp
  try ring_nf
  nlinarith

theorem m03_recip9 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : x + y = 1) :
    9 ≤ (1 + 1 / x) * (1 + 1 / y) := by
  have hprod : x * y ≤ 1 / 4 := by exact?
  have hprod_pos : 0 < x * y := by simp_all
  have hexp : (1 + 1 / x) * (1 + 1 / y) = 1 + 2 / (x * y) := by exact?
  have hdiv : 2 / (x * y) ≥ 8 := by exact?
  linarith
