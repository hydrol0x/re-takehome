import Mathlib

/-- If a real number `x` satisfies `x ^ 2 - 10 * x + 21 = 0`, then `x = 3` or `x = 7`. -/
theorem c01_quad_roots (x : ℝ) (h : x ^ 2 - 10 * x + 21 = 0) : x = 3 ∨ x = 7 := by
  have h_factored : (x - 3) * (x - 7) = 0 := by
    ring_nf at h ⊢
    linarith
  
  have h_cases : x - 3 = 0 ∨ x - 7 = 0 := by
    apply eq_zero_or_eq_zero_of_mul_eq_zero h_factored
  
  cases h_cases with
  | inl h1 =>
    have : x = 3 := by linarith
    exact Or.inl this
  | inr h2 =>
    have : x = 7 := by linarith
    exact Or.inr this
