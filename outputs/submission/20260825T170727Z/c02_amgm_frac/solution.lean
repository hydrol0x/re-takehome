import Mathlib

/-- For every positive real `x`, `x + 4 / x ≥ 4`. -/
theorem c02_amgm_frac (x : ℝ) (hx : 0 < x) : x + 4 / x ≥ 4 := by
  have h : (x - 2)^2 ≥ 0 := sq_nonneg (x - 2)
  have h1 : x^2 - 4*x + 4 ≥ 0 := by
    simp [sq] at h ⊢
    linarith
  have h2 : x^2 + 4 ≥ 4*x := by linarith
  have h3 : x + 4 / x ≥ 4 := by
    have hx_pos : 0 < x := hx
    have h4 : x + 4 / x - 4 = (x^2 - 4*x + 4) / x := by
      field_simp [hx_pos.ne']
      ring
    have h5 : (x^2 - 4*x + 4) / x ≥ 0 := by
      apply div_nonneg
      · linarith
      · linarith
    linarith
  exact h3
