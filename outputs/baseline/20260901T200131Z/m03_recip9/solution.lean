import Mathlib

/-- If `x` and `y` are positive reals with `x + y = 1`, then
`(1 + 1/x) * (1 + 1/y) ≥ 9`. -/
theorem m03_recip9 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : x + y = 1) :
    9 ≤ (1 + 1 / x) * (1 + 1 / y) := by
  have hxy_pos : 0 < x * y := mul_pos hx hy
  have h_xy_le : x * y ≤ 1 / 4 := by
    have h_sq : (x - y)^2 ≥ 0 := sq_nonneg _
    have h_expand : (x - y)^2 = x^2 - 2*x*y + y^2 := by ring
    have h_sum_sq : (x + y)^2 = x^2 + 2*x*y + y^2 := by ring
    have h_sub : (x + y)^2 - 4*x*y = x^2 - 2*x*y + y^2 := by ring
    calc
      0 ≤ (x - y)^2 := h_sq
      _ = x^2 - 2*x*y + y^2 := by rw [h_expand]
      _ = (x + y)^2 - 4*x*y := by rw [h_sub]
      _ = 1 - 4*x*y := by rw [h]
      _ ≤ 0 := by linarith
    linarith
  
  have h_inv_ge_4 : 1 / (x * y) ≥ 4 := by
    have h_xy_pos : 0 < x * y := hxy_pos
    have h_xy_le' : x * y ≤ 1 / 4 := h_xy_le
    calc
      1 / (x * y) ≥ 1 / (1 / 4) := by
        apply one_div_le_one_div_of_le
        · positivity
        · exact h_xy_le'
      _ = 4 := by norm_num
  
  calc
    9 = 1 + 8 := by norm_num
    _ ≤ 1 + 2 * (1 / (x * y)) := by
      have h_inv_ge_4' : 1 / (x * y) ≥ 4 := h_inv_ge_4
      nlinarith
    _ = 1 + 2 / (x * y) := by ring
    _ = (1 + 1 / x) * (1 + 1 / y) := by
      field_simp [hx.ne', hy.ne']
      ring
      <;> simp_all
      <;> field_simp [hx.ne', hy.ne']
      <;> ring
