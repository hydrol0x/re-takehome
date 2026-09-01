import Mathlib

/-- If `x` and `y` are positive reals with `x + y = 1`, then
`(1 + 1/x) * (1 + 1/y) ≥ 9`. -/
theorem m03_recip9 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : x + y = 1) :
    9 ≤ (1 + 1 / x) * (1 + 1 / y) := by
  have hxy : x * y ≤ 1 / 4 := by
    have h1 : (x - y) ^ 2 ≥ 0 := sq_nonneg (x - y)
    have h2 : (x + y) ^ 2 = 1 := by rw [h]; norm_num
    have h3 : 0 ≤ (x + y) ^ 2 - 4 * x * y := by
      calc
        0 ≤ (x - y) ^ 2 := h1
        _ = (x + y) ^ 2 - 4 * x * y := by ring
    have h4 : 0 ≤ 1 - 4 * x * y := by
      calc
        0 ≤ (x + y) ^ 2 - 4 * x * y := h3
        _ = 1 - 4 * x * y := by rw [h2]
    linarith
  
  have hmain : 9 ≤ (1 + 1 / x) * (1 + 1 / y) := by
    have h1 : 0 < x * y := mul_pos hx hy
    have h2 : (1 + 1 / x) * (1 + 1 / y) = 1 + 2 / (x * y) := by
      field_simp [hx.ne', hy.ne']
      ring
    rw [h2]
    have h3 : 2 / (x * y) ≥ 8 := by
      have h4 : x * y ≤ 1 / 4 := hxy
      have h5 : 0 < x * y := mul_pos hx hy
      calc
        2 / (x * y) ≥ 2 / (1 / 4) := by
          apply (div_le_div_iff (by positivity) (by positivity)).mpr
          nlinarith
        _ = 8 := by norm_num
    linarith
  
  exact hmain
