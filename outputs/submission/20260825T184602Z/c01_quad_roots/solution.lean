import Mathlib

/-- If a real number `x` satisfies `x ^ 2 - 10 * x + 21 = 0`, then `x = 3` or `x = 7`. -/
theorem c01_quad_roots (x : ℝ) (h : x ^ 2 - 10 * x + 21 = 0) : x = 3 ∨ x = 7 := by
  have h_factor : (x - 3) * (x - 7) = 0 := by
    rw [show x ^ 2 - 10 * x + 21 = (x - 3) * (x - 7) by ring] at h
    exact h
  
  -- If a product is zero, one of the factors must be zero
  cases' eq_zero_or_eq_zero_of_mul_eq_zero h_factor with h_left h_right
  · -- Case: x - 3 = 0
    left
    linarith
  · -- Case: x - 7 = 0
    right
    linarith
