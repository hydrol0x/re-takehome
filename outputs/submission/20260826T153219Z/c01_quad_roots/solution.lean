import Mathlib

/-- If a real number `x` satisfies `x ^ 2 - 10 * x + 21 = 0`, then `x = 3` or `x = 7`. -/
theorem c01_quad_roots (x : ℝ) (h : x ^ 2 - 10 * x + 21 = 0) : x = 3 ∨ x = 7 := by
  have h1 : (x - 3) * (x - 7) = 0 := by
    ring_nf at h ⊢
    linarith
  
  have h2 : x - 3 = 0 ∨ x - 7 = 0 := by
    apply eq_zero_or_eq_zero_of_mul_eq_zero h1
  
  cases' h2 with h2 h2
  · -- Case: x - 3 = 0
    apply Or.inl
    linarith
  · -- Case: x - 7 = 0
    apply Or.inr
    linarith
