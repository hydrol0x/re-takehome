import Mathlib

/-- AM–GM for three factors: positive reals `a, b, c` satisfy
`8 * (a * b * c) ≤ (a + b) * (b + c) * (c + a)`. -/
theorem m08_amgm8 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    8 * (a * b * c) ≤ (a + b) * (b + c) * (c + a) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]
