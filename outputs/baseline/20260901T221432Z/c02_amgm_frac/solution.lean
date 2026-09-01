import Mathlib

/-- For every positive real `x`, `x + 4 / x ≥ 4`. -/
theorem c02_amgm_frac (x : ℝ) (hx : 0 < x) : x + 4 / x ≥ 4 := by
  have hxne : x ≠ 0 := ne_of_gt hx
  -- start from the obvious non‑negativity of a square
  have h_sq : (x - 2) ^ 2 ≥ (0 : ℝ) := by
    exact sq_nonneg (x - 2)
  -- rewrite the square
  have h_poly : x ^ 2 - 4 * x + 4 ≥ (0 : ℝ) := by
    simpa [pow_two, sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc,
      add_comm, add_left_comm, add_assoc] using h_sq
  -- turn it into the desired polynomial inequality
  have h' : 4 * x ≤ x ^ 2 + 4 := by
    linarith
  -- divide by the positive `x`
  have hdiv : (4 * x) / x ≤ (x ^ 2 + 4) / x := (div_le_div_right hx).mpr h'
  -- simplify both sides
  have : 4 ≤ x + 4 / x := by
    have := hdiv
    field_simp [hxne] at this
    simpa [add_comm, add_left_comm, add_assoc] using this
  exact this
