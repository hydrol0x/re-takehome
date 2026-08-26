import Mathlib

/-- For every positive real `x`, `x + 4 / x ≥ 4`. -/
theorem c02_amgm_frac (x : ℝ) (hx : 0 < x) : x + 4 / x ≥ 4 := by
  have h : (x - 2)^2 ≥ 0 := sq_nonneg _
  have h1 : x + 4 / x - 4 = (x - 2)^2 / x := by
    field_simp [hx.ne']
    ring
  have h2 : (x - 2)^2 / x ≥ 0 := by
    exact div_nonneg h (le_of_lt hx)
  linarith
