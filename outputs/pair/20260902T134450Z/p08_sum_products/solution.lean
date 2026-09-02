import Mathlib

/-- Positive reals `a, b, c` with `a + b + c = 3` satisfy `a*b + b*c + c*a ≤ 3`. -/
theorem p08_sum_products (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 3) : a * b + b * c + c * a ≤ 3 := by
  have h1 : (a + b + c)^2 = a^2 + b^2 + c^2 + 2 * (a * b + b * c + c * a) := by
    ring
  rw [h] at h1
  have h2 : 9 = a^2 + b^2 + c^2 + 2 * (a * b + b * c + c * a) := by linarith
  
  -- Use the fact that (a-b)^2 + (b-c)^2 + (c-a)^2 ≥ 0
  have h3 : 0 ≤ (a - b)^2 + (b - c)^2 + (c - a)^2 := by nlinarith
  have h4 : 0 ≤ 2 * (a^2 + b^2 + c^2) - 2 * (a * b + b * c + c * a) := by
    linarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  
  -- From h4: a^2 + b^2 + c^2 ≥ a*b + b*c + c*a
  have h5 : a^2 + b^2 + c^2 ≥ a * b + b * c + c * a := by linarith
  
  -- Substitute into h2: 9 = a^2 + b^2 + c^2 + 2*(a*b + b*c + c*a)
  -- Since a^2 + b^2 + c^2 ≥ a*b + b*c + c*a, we get:
  -- 9 ≥ 3*(a*b + b*c + c*a), so a*b + b*c + c*a ≤ 3
  nlinarith
