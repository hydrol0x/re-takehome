import Mathlib

/-- If a real number `x` satisfies `x ^ 2 - 10 * x + 21 = 0`, then `x = 3` or `x = 7`. -/
theorem c01_quad_roots (x : ℝ) (h : x ^ 2 - 10 * x + 21 = 0) : x = 3 ∨ x = 7 := by
  have h_factored : (x - 3) * (x - 7) = 0 := by
    have : x ^ 2 - 10 * x + 21 = (x - 3) * (x - 7) := by ring
    rw [this] at h
    exact h
  
  have h_cases : x - 3 = 0 ∨ x - 7 = 0 := eq_zero_or_eq_zero_of_mul_eq_zero h_factored
  
  cases h_cases with
  | inl h_left =>
    left
    linarith
  | inr h_right =>
    right
    linarith
