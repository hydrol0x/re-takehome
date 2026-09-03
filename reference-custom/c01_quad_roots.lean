import Mathlib

/-- If a real number `x` satisfies `x ^ 2 - 10 * x + 21 = 0`, then `x = 3` or `x = 7`. -/
theorem c01_quad_roots (x : ℝ) (h : x ^ 2 - 10 * x + 21 = 0) : x = 3 ∨ x = 7 := by
  have h2 : (x - 3) * (x - 7) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h3 | h3
  · left; linarith
  · right; linarith
