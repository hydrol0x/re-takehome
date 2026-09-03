import Mathlib

/-- If `x` and `y` are positive reals with `x + y = 1`, then
`(1 + 1/x) * (1 + 1/y) ≥ 9`. -/
theorem m03_recip9 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : x + y = 1) :
    9 ≤ (1 + 1 / x) * (1 + 1 / y) := by
  have h₁ : 0 < x * y := mul_pos hx hy
  have h₂ : (x - y) ^ 2 ≥ 0 := sq_nonneg (x - y)
  have h₃ : x * y ≤ 1 / 4 := by
    nlinarith [sq_nonneg (x - y)]
  have h₄ : 2 / (x * y) ≥ 8 := by
    have h₅ : 0 < x * y := mul_pos hx hy
    have h₆ : x * y ≤ 1 / 4 := h₃
    calc
      2 / (x * y) ≥ 2 / (1 / 4) := by gcongr <;> linarith
      _ = 8 := by norm_num
  calc
    9 = 1 + 8 := by norm_num
    _ ≤ 1 + 2 / (x * y) := by linarith
    _ = (x * y + 2) / (x * y) := by field_simp [h₁.ne'] <;> ring
    _ = (x * y + x + y + 1) / (x * y) := by rw [h]; ring
    _ = ((x + 1) * (y + 1)) / (x * y) := by ring
    _ = (1 + 1 / x) * (1 + 1 / y) := by
      field_simp [hx.ne', hy.ne']
      <;> ring
      <;> field_simp [hx.ne', hy.ne']
      <;> ring
