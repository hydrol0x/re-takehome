import Mathlib

/-- If `x` and `y` are positive reals with `x + y = 1`, then
`(1 + 1/x) * (1 + 1/y) ≥ 9`. -/
theorem m03_recip9 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : x + y = 1) :
    9 ≤ (1 + 1 / x) * (1 + 1 / y) := by
  have hxy_pos : 0 < x * y := mul_pos hx hy
  have h_denom_ne_zero : x ≠ 0 ∧ y ≠ 0 := ⟨ne_of_gt hx, ne_of_gt hy⟩
  
  -- Clear denominators: multiply both sides by xy
  have h_main : 9 * x * y ≤ (x + 1) * (y + 1) := by
    rw [← h]
    ring_nf
    nlinarith [sq_nonneg (x - y)]
  
  -- Divide back by xy to get the original inequality
  have h_result : 9 ≤ (1 + 1 / x) * (1 + 1 / y) := by
    calc
      9 = 9 * x * y / (x * y) := by field_simp [hxy_pos.ne'] <;> ring
      _ ≤ (x + 1) * (y + 1) / (x * y) := by
        gcongr
        <;> linarith
      _ = (1 + 1 / x) * (1 + 1 / y) := by
        field_simp [h_denom_ne_zero.1, h_denom_ne_zero.2]
        <;> ring
  
  exact h_result
