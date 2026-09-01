import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Real.Basic

/-- AM–GM for three factors: positive reals `a, b, c` satisfy
`8 * (a * b * c) ≤ (a + b) * (b + c) * (c + a)`. -/
theorem m08_amgm8 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    8 * (a * b * c) ≤ (a + b) * (b + c) * (c + a) := by
  have h1 : (a + b) * (b + c) * (c + a) - 8 * (a * b * c) = a * (b - c)^2 + b * (c - a)^2 + c * (a - b)^2 := by
    ring_nf
    <;>
    linarith
  
  have h2 : a * (b - c)^2 + b * (c - a)^2 + c * (a - b)^2 ≥ 0 := by
    have h3 : a * (b - c)^2 ≥ 0 := by
      exact mul_nonneg ha.le (sq_nonneg _)
    have h4 : b * (c - a)^2 ≥ 0 := by
      exact mul_nonneg hb.le (sq_nonneg _)
    have h5 : c * (a - b)^2 ≥ 0 := by
      exact mul_nonneg hc.le (sq_nonneg _)
    linarith
  
  linarith
