import Mathlib

/-- If a real number `x` satisfies `x ^ 2 - 10 * x + 21 = 0`, then `x = 3` or `x = 7`. -/
theorem c01_quad_roots (x : ℝ) (h : x ^ 2 - 10 * x + 21 = 0) : x = 3 ∨ x = 7 := by
  have h₁ : (x - 3) * (x - 7) = 0 := by
    ring_nf at h ⊢
    linarith
  have h₂ : x - 3 = 0 ∨ x - 7 = 0 := by
    apply eq_zero_or_eq_zero_of_mul_eq_zero h₁
  cases h₂ with
  | inl h₂ =>
    have h₃ : x = 3 := by linarith
    exact Or.inl h₃
  | inr h₂ =>
    have h₃ : x = 7 := by linarith
    exact Or.inr h₃
