import Mathlib

/-- If a real number `x` satisfies `x ^ 2 - 10 * x + 21 = 0`, then `x = 3` or `x = 7`. -/
theorem c01_quad_roots (x : ℝ) (h : x ^ 2 - 10 * x + 21 = 0) : x = 3 ∨ x = 7 := by
  have h' : (x - 3) * (x - 7) = 0 := by
    have : x ^ 2 - 10 * x + 21 = (x - 3) * (x - 7) := by
      ring
    simpa [this] using h
  rcases mul_eq_zero.mp h' with hleft | hright
  · left
    exact sub_eq_zero.mp hleft
  · right
    exact sub_eq_zero.mp hright
