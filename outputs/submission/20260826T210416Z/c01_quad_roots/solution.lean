import Mathlib

/-- If a real number `x` satisfies `x ^ 2 - 10 * x + 21 = 0`, then `x = 3` or `x = 7`. -/
theorem c01_quad_roots (x : ℝ) (h : x ^ 2 - 10 * x + 21 = 0) : x = 3 ∨ x = 7 := by
  have h_factored : (x - 3) * (x - 7) = 0 := by
    rw [show x ^ 2 - 10 * x + 21 = (x - 3) * (x - 7) by ring] at h
    exact h
  
  -- In a field, if a product equals zero, one of the factors must be zero
  have h_factor : x - 3 = 0 ∨ x - 7 = 0 := by
    apply eq_zero_or_eq_zero_of_mul_eq_zero
    exact h_factored
  
  cases' h_factor with h3 h7
  · -- Case: x - 3 = 0, so x = 3
    have : x = 3 := by linarith
    exact Or.inl this
  · -- Case: x - 7 = 0, so x = 7
    have : x = 7 := by linarith
    exact Or.inr this
