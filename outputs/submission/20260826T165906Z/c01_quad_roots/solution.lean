import Mathlib

/-- If a real number `x` satisfies `x ^ 2 - 10 * x + 21 = 0`, then `x = 3` or `x = 7`. -/
theorem c01_quad_roots (x : ℝ) (h : x ^ 2 - 10 * x + 21 = 0) : x = 3 ∨ x = 7 := by
  have h₁ : (x - 3) * (x - 7) = 0 := by
    calc
      (x - 3) * (x - 7) = x ^ 2 - 7 * x - 3 * x + 21 := by ring
      _ = x ^ 2 - 10 * x + 21 := by ring
      _ = 0 := h
  have h₂ : x - 3 = 0 ∨ x - 7 = 0 := by
    simpa [sub_eq_zero] using eq_zero_or_eq_zero_of_mul_eq_zero h₁
  cases h₂ with
  | inl h₃ =>
    left
    linarith
  | inr h₃ =>
    right
    linarith
