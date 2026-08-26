import Mathlib

/-- If a real number `x` satisfies `x ^ 2 - 10 * x + 21 = 0`, then `x = 3` or `x = 7`. -/
theorem c01_quad_roots (x : ℝ) (h : x ^ 2 - 10 * x + 21 = 0) : x = 3 ∨ x = 7 := by
  have h1 : (x - 3) * (x - 7) = 0 := by
    calc
      (x - 3) * (x - 7) = x ^ 2 - 7 * x - 3 * x + 21 := by ring
      _ = x ^ 2 - 10 * x + 21 := by ring
      _ = 0 := h
  
  have h2 : x - 3 = 0 ∨ x - 7 = 0 := by
    apply eq_zero_or_eq_zero_of_mul_eq_zero h1
  
  cases h2 with
  | inl h3 =>
    have h4 : x = 3 := by linarith
    exact Or.inl h4
  | inr h5 =>
    have h6 : x = 7 := by linarith
    exact Or.inr h6
