import Mathlib

/-- For every positive real `x`, `x + 4 / x ≥ 4`. -/
theorem c02_amgm_frac (x : ℝ) (hx : 0 < x) : x + 4 / x ≥ 4 := by
  have h : (x - 2) ^ 2 ≥ 0 := sq_nonneg (x - 2)
  have h2 : x ^ 2 - 4 * x + 4 ≥ 0 := by
    calc
      x ^ 2 - 4 * x + 4 = (x - 2) ^ 2 := by ring
      _ ≥ 0 := h
  have h3 : x + 4 / x - 4 ≥ 0 := by
    have h4 : x * (x + 4 / x - 4) = x ^ 2 - 4 * x + 4 := by
      field_simp [hx.ne']
      <;> ring
    have h5 : x * (x + 4 / x - 4) ≥ 0 := by
      rw [h4]
      exact h2
    have h6 : x + 4 / x - 4 ≥ 0 := by
      by_contra h7
      have h8 : x + 4 / x - 4 < 0 := by linarith
      have h9 : x * (x + 4 / x - 4) < 0 := by
        nlinarith
      linarith
    exact h6
  linarith
