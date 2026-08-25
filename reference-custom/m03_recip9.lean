import Mathlib

/-- If `x` and `y` are positive reals with `x + y = 1`, then
`(1 + 1/x) * (1 + 1/y) ≥ 9`. -/
theorem m03_recip9 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : x + y = 1) :
    9 ≤ (1 + 1 / x) * (1 + 1 / y) := by
  have hxy : 0 < x * y := mul_pos hx hy
  have hkey : 9 * (x * y) ≤ (x + 1) * (y + 1) := by nlinarith [sq_nonneg (x - y)]
  have hexp : (1 + 1 / x) * (1 + 1 / y) = (x + 1) * (y + 1) / (x * y) := by
    field_simp
  rw [hexp, le_div_iff₀ hxy]
  linarith [hkey]
