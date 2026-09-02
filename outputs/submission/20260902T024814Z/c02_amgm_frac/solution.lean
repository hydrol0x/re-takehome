import Mathlib

/-- For every positive real `x`, `x + 4 / x ≥ 4`. -/
theorem c02_amgm_frac (x : ℝ) (hx : 0 < x) : x + 4 / x ≥ 4 := by
  have h_eq : x + 4 / x - 4 = (x - 2) ^ 2 / x := by calc
    x + 4 / x - 4 = (x * x + 4 - 4 * x) / x := by
      field_simp [hx.ne']
      <;> ring
    _ = ((x - 2) ^ 2) / x := by
      ring
  have h_sq_nonneg : 0 ≤ (x - 2) ^ 2 := by positivity
  have h_div_nonneg : 0 ≤ (x - 2) ^ 2 / x := by positivity
  have h_main : x + 4 / x ≥ 4 := by linarith
  exact h_main