import Mathlib

/-- If `x` and `y` are positive reals with `x + y = 1`, then
`(1 + 1/x) * (1 + 1/y) ≥ 9`. -/
theorem m03_recip9 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : x + y = 1) :
    9 ≤ (1 + 1 / x) * (1 + 1 / y) := by
  have hxy_pos : 0 < x * y := mul_pos hx hy
  have hxy_le : x * y ≤ 1 / 4 := by
    have h_sq : (x - y) ^ 2 ≥ 0 := sq_nonneg _
    have h_expand : (x - y) ^ 2 = x ^ 2 - 2 * x * y + y ^ 2 := by ring
    rw [h_expand] at h_sq
    have h_sum_sq : (x + y) ^ 2 = 1 := by rw [h]; norm_num
    have h_sum_sq_exp : (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by ring
    rw [h_sum_sq_exp] at h_sum_sq
    nlinarith
  have h_main : 1 / (x * y) ≥ 4 := by
    have h_inv : 0 < x * y := hxy_pos
    have h_ineq : x * y ≤ 1 / 4 := hxy_le
    calc
      1 / (x * y) ≥ 1 / (1 / 4) := one_div_le_one_div_of_le h_ineq h_inv.le
      _ = 4 := by norm_num
  calc
    9 = 1 + 8 := by norm_num
    _ ≤ 1 + 2 * (1 / (x * y)) := by
      have h_ineq : 8 ≤ 2 * (1 / (x * y)) := by
        calc
          8 = 2 * 4 := by norm_num
          _ ≤ 2 * (1 / (x * y)) := by gcongr
      linarith
    _ = 1 + 2 / (x * y) := by field_simp
    _ = 1 + 1 / x + 1 / y + 1 / (x * y) := by
      have h_sum : x + y = 1 := h
      have h_frac : 1 / x + 1 / y = (x + y) / (x * y) := by
        field_simp [hx.ne', hy.ne']
        ring
      rw [h_frac, h_sum]
      field_simp [hx.ne', hy.ne']
      ring
    _ = (1 + 1 / x) * (1 + 1 / y) := by
      field_simp [hx.ne', hy.ne']
      ring
