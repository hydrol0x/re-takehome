import Mathlib

/-- AM–GM for three factors: positive reals `a, b, c` satisfy
`8 * (a * b * c) ≤ (a + b) * (b + c) * (c + a)`. -/
theorem m08_amgm8 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    8 * (a * b * c) ≤ (a + b) * (b + c) * (c + a) := by
  have h_main : (a + b) * (b + c) * (c + a) - 8 * (a * b * c) = a * (b - c)^2 + b * (c - a)^2 + c * (a - b)^2 := by
    ring_nf
    <;>
    linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  
  have h_nonneg : a * (b - c)^2 + b * (c - a)^2 + c * (a - b)^2 ≥ 0 := by
    have h1 : a * (b - c)^2 ≥ 0 := by
      apply mul_nonneg ha.le
      exact sq_nonneg _
    have h2 : b * (c - a)^2 ≥ 0 := by
      apply mul_nonneg hb.le
      exact sq_nonneg _
    have h3 : c * (a - b)^2 ≥ 0 := by
      apply mul_nonneg hc.le
      exact sq_nonneg _
    linarith
  
  linarith
