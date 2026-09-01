import Mathlib

/-- If `x` and `y` are positive reals with `x + y = 1`, then
`(1 + 1/x) * (1 + 1/y) ≥ 9`. -/
theorem m03_recip9 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : x + y = 1) :
    9 ≤ (1 + 1 / x) * (1 + 1 / y) := by
  -- positivity of the product
  have hpos : 0 < x * y := mul_pos hx hy
  have hxne : x ≠ 0 := ne_of_gt hx
  have hyne : y ≠ 0 := ne_of_gt hy

  -- a useful inequality: 4·x·y ≤ 1
  have h4xy : (4 : ℝ) * x * y ≤ (1 : ℝ) := by
    have h_nonneg : (0 : ℝ) ≤ (x - y) ^ 2 := by
      exact sq_nonneg (x - y)
    have h_eq : (x - y) ^ 2 = (x + y) ^ 2 - 4 * x * y := by
      ring
    have : (x + y) ^ 2 - 4 * x * y ≥ 0 := by
      simpa [h_eq] using h_nonneg
    have : (x + y) ^ 2 ≥ 4 * x * y := by
      linarith
    simpa [h] using this

  -- from the previous inequality we get 9·x·y ≤ (x+1)(y+1)
  have h9xy : (9 : ℝ) * x * y ≤ (x + 1) * (y + 1) := by
    have h8xy : (8 : ℝ) * x * y ≤ (2 : ℝ) := by
      have : (4 : ℝ) * x * y ≤ (1 : ℝ) := h4xy
      linarith
    have : (9 : ℝ) * x * y ≤ x * y + 2 := by
      have : (8 : ℝ) * x * y ≤ (2 : ℝ) := h8xy
      linarith
    simpa [mul_add, add_mul, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc, h, mul_one, one_mul] using this

  -- turn the inequality into the desired form using division by the positive product
  have hle : (9 : ℝ) ≤ ((x + 1) * (y + 1)) / (x * y) := by
    exact (le_div_iff hpos).mpr h9xy

  -- rewrite the right‑hand side
  have h_eq : (1 + 1 / x) * (1 + 1 / y) = ((x + 1) * (y + 1)) / (x * y) := by
    field_simp [hxne, hyne]

  simpa [h_eq] using hle
