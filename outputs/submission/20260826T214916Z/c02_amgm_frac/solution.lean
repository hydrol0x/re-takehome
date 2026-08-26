import Mathlib

/-- For every positive real `x`, `x + 4 / x ≥ 4`. -/
theorem c02_amgm_frac (x : ℝ) (hx : 0 < x) : x + 4 / x ≥ 4 := by
  have h_main : x + 4 / x - 4 = (x - 2) ^ 2 / x := by
    field_simp [hx.ne']
    ring
    <;> linarith
  
  have h_sq_nonneg : (x - 2) ^ 2 / x ≥ 0 := by
    apply div_nonneg
    · exact sq_nonneg (x - 2)
    · exact hx.le
  
  linarith
