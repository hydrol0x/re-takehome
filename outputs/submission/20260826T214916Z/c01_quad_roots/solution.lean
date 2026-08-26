import Mathlib

/-- If a real number `x` satisfies `x ^ 2 - 10 * x + 21 = 0`, then `x = 3` or `x = 7`. -/
theorem c01_quad_roots (x : ℝ) (h : x ^ 2 - 10 * x + 21 = 0) : x = 3 ∨ x = 7 := by
  have h_factored : (x - 3) * (x - 7) = 0 := by
    calc
      (x - 3) * (x - 7) = x ^ 2 - 10 * x + 21 := by ring
      _ = 0 := h
  -- A product equals zero iff one of the factors equals zero
  have h_factors : x - 3 = 0 ∨ x - 7 = 0 := by
    apply eq_zero_or_eq_zero_of_mul_eq_zero h_factored
  -- Case analysis on which factor is zero
  cases h_factors with
  | inl h_left =>
    have : x = 3 := by linarith
    exact Or.inl this
  | inr h_right =>
    have : x = 7 := by linarith
    exact Or.inr this
