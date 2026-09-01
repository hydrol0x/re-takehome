import Mathlib

/-- If `x` and `y` are positive reals with `x + y = 1`, then
`(1 + 1/x) * (1 + 1/y) ≥ 9`. -/
theorem m03_recip9 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : x + y = 1) :
    9 ≤ (1 + 1 / x) * (1 + 1 / y) := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hy0 : y ≠ 0 := ne_of_gt hy
  field_simp [hx0, hy0] at *
  -- goal is now `9 ≤ ((x + 1) * (y + 1)) / (x * y)`
  have hpos : 0 < x * y := mul_pos hx hy
  have hxy_mul : 9 * (x * y) ≤ (x + 1) * (y + 1) := by
    have hxy_expand : (x + 1) * (y + 1) = x * y + 2 := by
      calc
        (x + 1) * (y + 1) = x * y + x + y + 1 := by ring
        _ = x * y + (x + y) + 1 := by ring
        _ = x * y + 1 + 1 := by simpa [h]
        _ = x * y + 2 := by ring
    have : 9 * (x * y) ≤ x * y + 2 := by
      have h4 : (4 : ℝ) * x * y ≤ 1 := by
        have hsq : (x - y) ^ 2 ≥ (0 : ℝ) := by
          exact pow_two_nonneg _
        have : (x + y) ^ 2 - 4 * x * y ≥ 0 := by
          simpa [pow_two, mul_add, add_mul, sub_eq_add_neg,
            add_comm, add_left_comm, add_assoc,
            mul_comm, mul_left_comm, mul_assoc] using hsq
        have : 1 - 4 * x * y ≥ 0 := by
          simpa [h] using this
        have : 4 * x * y ≤ 1 := by
          have := sub_nonneg.mp this
          simpa [mul_comm, mul_left_comm, mul_assoc] using this
        exact this
      have h8 : (8 : ℝ) * x * y ≤ 2 := by
        have := mul_le_mul_of_nonneg_left h4 (by norm_num : (0 : ℝ) ≤ (2 : ℝ))
        simpa [two_mul, mul_comm, mul_left_comm, mul_assoc] using this
      have : 9 * (x * y) = 8 * (x * y) + (x * y) := by ring
      have : 8 * (x * y) + (x * y) ≤ 2 + (x * y) := add_le_add_right h8 _
      simpa [add_comm, add_left_comm, add_assoc] using this
    simpa [hxy_expand] using this
  have : 9 ≤ ((x + 1) * (y + 1)) / (x * y) := (le_div_iff hpos).mpr hxy_mul
  exact this
