import Mathlib

/-- For every positive real `x`, `x + 4 / x ≥ 4`. -/
theorem c02_amgm_frac (x : ℝ) (hx : 0 < x) : x + 4 / x ≥ 4 := by
  rw [ge_iff_le, ← sub_nonneg]
  have hx' : x ≠ 0 := ne_of_gt hx
  have h : x + 4 / x - 4 = (x - 2) ^ 2 / x := by
    field_simp
    ring
  rw [h]
  positivity
