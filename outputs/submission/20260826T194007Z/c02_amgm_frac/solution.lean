import Mathlib

/-- For every positive real `x`, `x + 4 / x ≥ 4`. -/
theorem c02_amgm_frac (x : ℝ) (hx : 0 < x) : x + 4 / x ≥ 4 := by
  have h₁ : x + 4 / x - 4 = (x - 2) ^ 2 / x := by
    field_simp [hx.ne']
    ring
    <;> field_simp [hx.ne']
    <;> ring
  
  have h₂ : 0 ≤ (x - 2) ^ 2 := by
    exact sq_nonneg _
  
  have h₃ : 0 ≤ (x - 2) ^ 2 / x := by
    exact div_nonneg h₂ hx.le
  
  linarith
