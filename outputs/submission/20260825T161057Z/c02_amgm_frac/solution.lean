import Mathlib

/-- For every positive real `x`, `x + 4 / x ≥ 4`. -/
theorem c02_amgm_frac (x : ℝ) (hx : 0 < x) : x + 4 / x ≥ 4 := by
  have h : (x - 2) ^ 2 ≥ 0 := by nlinarith [sq_nonneg (x - 2)]
  have h₁ : x + 4 / x - 4 = (x - 2) ^ 2 / x := by
    field_simp [hx.ne']
    ring
  have h₂ : (x - 2) ^ 2 / x ≥ 0 := by
    apply div_nonneg
    · exact h
    · linarith
  linarith
