import Mathlib

/-- For every positive real `x`, `x + 4 / x ≥ 4`. -/
theorem c02_amgm_frac (x : ℝ) (hx : 0 < x) : x + 4 / x ≥ 4 := by
  have hx0 : (x : ℝ) ≠ 0 := ne_of_gt hx
  -- Prove the equivalent polynomial inequality.
  have hpoly : x * x + 4 ≥ 4 * x := by
    have hsq : 0 ≤ (x - 2) ^ 2 := by
      exact sq_nonneg (x - 2)
    have hexpand : (x - 2) ^ 2 = x * x - 4 * x + 4 := by
      ring
    have : x * x - 4 * x + 4 ≥ 0 := by
      simpa [hexpand] using hsq
    linarith
  -- Translate back to the original statement.
  have : x + 4 / x ≥ 4 := by
    have h := hpoly
    field_simp [hx0] at h ⊢
    exact h
  exact this
