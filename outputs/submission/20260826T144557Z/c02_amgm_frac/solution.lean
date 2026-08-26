import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-- For every positive real `x`, `x + 4 / x ≥ 4`. -/
theorem c02_amgm_frac (x : ℝ) (hx : 0 < x) : x + 4 / x ≥ 4 := by
  have h1 : (x - 2)^2 ≥ 0 := by
    nlinarith [sq_nonneg (x - 2)]
  have h2 : x^2 - 4 * x + 4 = (x - 2)^2 := by
    ring
  have h3 : x + 4 / x - 4 = (x - 2)^2 / x := by
    field_simp [hx.ne']
    ring
  have h4 : (x - 2)^2 / x ≥ 0 := by
    apply div_nonneg
    · exact sq_nonneg (x - 2)
    · linarith
  have h5 : x + 4 / x - 4 ≥ 0 := by
    linarith
  linarith
