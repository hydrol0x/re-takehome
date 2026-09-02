import Mathlib

/-- For every positive real `x`, `x + 4 / x ≥ 4`. -/
theorem c02_amgm_frac (x : ℝ) (hx : 0 < x) : x + 4 / x ≥ 4 := by
  have h₁ : x + 4 / x - 4 = (x - 2)^2 / x := by
    field_simp [hx.ne']
    ring
  have h₂ : (x - 2)^2 ≥ 0 := sq_nonneg _
  have h₃ : (x - 2)^2 / x ≥ 0 := div_nonneg h₂ hx.le
  have h₄ : x + 4 / x - 4 ≥ 0 := by
    rw [h₁]
    exact h₃
  linarith
