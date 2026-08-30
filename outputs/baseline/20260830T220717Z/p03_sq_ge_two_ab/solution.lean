import Mathlib

/-- For any two real numbers `a` and `b`, show that `a ^ 2 + b ^ 2 ≥ 2 * a * b`. -/
theorem p03_sq_ge_two_ab (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b := by
  have h_nonneg : (a - b) ^ 2 ≥ 0 := by
    have := mul_self_nonneg (a - b)
    simpa [pow_two] using this
  have h_eq : a ^ 2 + b ^ 2 - 2 * a * b = (a - b) ^ 2 := by
    ring
  have h_sub : a ^ 2 + b ^ 2 - 2 * a * b ≥ 0 := by
    simpa [h_eq] using h_nonneg
  exact (sub_nonneg.mp h_sub)
