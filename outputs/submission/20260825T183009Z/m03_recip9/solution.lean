import Mathlib

/-- If `x` and `y` are positive reals with `x + y = 1`, then
`(1 + 1/x) * (1 + 1/y) ≥ 9`. -/
theorem m03_recip9 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : x + y = 1) :
    9 ≤ (1 + 1 / x) * (1 + 1 / y) := by
  have hxy : 0 < x * y := mul_pos hx hy
  field_simp [hx.ne', hy.ne']
  rw [← sub_nonneg]
  ring_nf at h ⊢
  nlinarith [sq_nonneg (x - y)]
