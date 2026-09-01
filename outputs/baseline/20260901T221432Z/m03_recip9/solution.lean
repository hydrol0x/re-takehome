import Mathlib.Tactic
import Mathlib.Data.Real.Basic

/-- If `x` and `y` are positive reals with `x + y = 1`, then
`(1 + 1/x) * (1 + 1/y) ≥ 9`. -/
theorem m03_recip9 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : x + y = 1) :
    9 ≤ (1 + 1 / x) * (1 + 1 / y) := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hpos : 0 < x * y := mul_pos hx hy

  -- rewrite the product in a convenient form
  have hrew : (1 + 1 / x) * (1 + 1 / y) = (x + 1) * (y + 1) / (x * y) := by
    field_simp [hx0, hy0]

  -- it suffices to prove the inequality after clearing denominators
  have : 9 ≤ (x + 1) * (y + 1) / (x * y) := by
    -- use `le_div_iff` (denominator is positive)
    apply (le_div_iff hpos).mpr
    -- now we need `9 * (x*y) ≤ (x+1)*(y+1)`
    have hmul : (9 : ℝ) * (x * y) ≤ (x + 1) * (y + 1) := by
      -- simplify the right‑hand side using `h`
      have hxy : (x + 1) * (y + 1) = x * y + 2 := by
        have : (x + 1) * (y + 1) = x * y + x + y + 1 := by ring
        simpa [h, add_comm, add_left_comm, add_assoc] using this
      -- the goal becomes `9*x*y ≤ x*y + 2`
      have h4xy : (4 : ℝ) * x * y ≤ 1 := by
        -- from `(x - y)^2 ≥ 0` we obtain `4xy ≤ (x+y)^2 = 1`
        have hnonneg : (0 : ℝ) ≤ (x - y) ^ 2 := by nlinarith
        have hsub : (x + y) ^ 2 - 4 * x * y = (x - y) ^ 2 := by ring
        have : 0 ≤ (x + y) ^ 2 - 4 * x * y := by
          simpa [hsub] using hnonneg
        have : 4 * x * y ≤ (x + y) ^ 2 := (sub_nonneg.mp this)
        simpa [h] using this
      have h8xy : (8 : ℝ) * x * y ≤ 2 := by
        have := mul_le_mul_of_nonneg_left h4xy (by norm_num : (0 : ℝ) ≤ (2 : ℝ))
        simpa [two_mul, mul_comm, mul_left_comm, mul_assoc] using this
      calc
        (9 : ℝ) * x * y = (8 : ℝ) * x * y + x * y := by ring
        _ ≤ 2 + x * y := by
          have := add_le_add_right h8xy (x * y)
          simpa [add_comm, add_left_comm, add_assoc] using this
        _ = x * y + 2 := by ring
      simpa [hxy] using this
    exact hmul

  simpa [hrew] using this
