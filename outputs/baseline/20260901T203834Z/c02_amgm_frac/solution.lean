import Mathlib

/-- For every positive real `x`, `x + 4 / x ≥ 4`. -/
theorem c02_amgm_frac (x : ℝ) (hx : 0 < x) : x + 4 / x ≥ 4 := by
  have hxne : (x : ℝ) ≠ 0 := ne_of_gt hx
  have hsq : (x - 2) ^ 2 ≥ 0 := by
    have : (x - 2) * (x - 2) ≥ 0 := by
      exact mul_self_nonneg (x - 2)
    simpa [pow_two] using this
  have h_eq : x + 4 / x - 4 = (x - 2) ^ 2 / x := by
    field_simp [hxne]
    ring
  have h_nonneg : (x - 2) ^ 2 / x ≥ 0 := by
    exact div_nonneg hsq (le_of_lt hx)
  have h_sub : x + 4 / x - 4 ≥ 0 := by
    simpa [h_eq] using h_nonneg
  linarith
