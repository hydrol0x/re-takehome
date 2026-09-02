import Mathlib

/-- If `x` and `y` are positive reals with `x + y = 1`, then
`(1 + 1/x) * (1 + 1/y) ≥ 9`. -/
theorem m03_recip9 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : x + y = 1) :
    9 ≤ (1 + 1 / x) * (1 + 1 / y) := by
  have hxy_pos : 0 < x * y := mul_pos hx hy
  have hxy_le_1_4 : x * y ≤ 1 / 4 := by
    have : (x - y)^2 ≥ 0 := sq_nonneg (x - y)
    have : (x + y)^2 = 1 := by rw [h]; norm_num
    nlinarith
  calc
    9 ≤ 1 + 2 / (x * y) := by
      have : 0 < x * y := hxy_pos
      have : 2 / (x * y) ≥ 8 := by
        have : x * y ≤ 1 / 4 := hxy_le_1_4
        have : 0 < x * y := hxy_pos
        calc
          2 / (x * y) ≥ 2 / (1 / 4) := by gcongr <;> linarith
          _ = 8 := by norm_num
      linarith
    _ = (1 + 1 / x) * (1 + 1 / y) := by
      have : x ≠ 0 := ne_of_gt hx
      have : y ≠ 0 := ne_of_gt hy
      field_simp [this, this]
      ring
      <;> simp_all [add_comm, add_left_comm, add_assoc]
      <;> linarith
