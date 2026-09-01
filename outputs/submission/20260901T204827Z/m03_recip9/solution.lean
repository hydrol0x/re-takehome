import Mathlib

/-- If `x` and `y` are positive reals with `x + y = 1`, then
`(1 + 1/x) * (1 + 1/y) ≥ 9`. -/
theorem m03_recip9 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : x + y = 1) :
    9 ≤ (1 + 1 / x) * (1 + 1 / y) := by
  have h₁ : 0 < x * y := mul_pos hx hy
  have h₂ : (1 + 1 / x) * (1 + 1 / y) - 9 ≥ 0 := by
    field_simp [hx.ne', hy.ne']
    rw [le_sub_iff_add_le]
    rw [← sub_nonneg]
    have h₃ : (x + y) ^ 2 = 1 := by
      rw [h]
      norm_num
    have h₄ : 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)
    nlinarith [sq_nonneg (x - y), h₃]
  linarith
