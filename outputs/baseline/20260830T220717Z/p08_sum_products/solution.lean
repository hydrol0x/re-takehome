import Mathlib

/-- Positive reals `a, b, c` with `a + b + c = 3` satisfy `a*b + b*c + c*a ≤ 3`. -/
theorem p08_sum_products (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 3) : a * b + b * c + c * a ≤ 3 := by
  -- First we show `a^2 + b^2 + c^2 ≥ ab + bc + ca`.
  have hineq : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a := by
    have h_nonneg : (0 : ℝ) ≤ (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 := by
      have h1 : (0 : ℝ) ≤ (a - b) ^ 2 := by exact sq_nonneg _
      have h2 : (0 : ℝ) ≤ (b - c) ^ 2 := by exact sq_nonneg _
      have h3 : (0 : ℝ) ≤ (c - a) ^ 2 := by exact sq_nonneg _
      have : (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 ≥ 0 :=
        add_nonneg (add_nonneg h1 h2) h3
      exact this
    have h_eq :
        (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2 =
          2 * (a ^ 2 + b ^ 2 + c ^ 2 - (a * b + b * c + c * a)) := by
      ring
    have : (0 : ℝ) ≤
        2 * (a ^ 2 + b ^ 2 + c ^ 2 - (a * b + b * c + c * a)) := by
      simpa [h_eq] using h_nonneg
    have : (0 : ℝ) ≤ a ^ 2 + b ^ 2 + c ^ 2 - (a * b + b * c + c * a) := by
      have : (0 : ℝ) ≤ (2 : ℝ) *
          (a ^ 2 + b ^ 2 + c ^ 2 - (a * b + b * c + c * a)) := by
        simpa [h_eq] using h_nonneg
      nlinarith
    linarith
  -- Relate the sum of squares to the square of the sum.
  have hsum_sq :
      (a + b + c) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a * b + b * c + c * a) := by
    ring
  -- From the previous inequality we obtain `3 * (ab+bc+ca) ≤ (a+b+c)^2`.
  have h3 : 3 * (a * b + b * c + c * a) ≤ (a + b + c) ^ 2 := by
    have : a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a * b + b * c + c * a) ≥
        3 * (a * b + b * c + c * a) := by
      have : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a := hineq
      linarith
    simpa [hsum_sq] using this
  -- Using `a + b + c = 3` we get the desired bound.
  have : a * b + b * c + c * a ≤ 3 := by
    have : 3 * (a * b + b * c + c * a) ≤ 9 := by
      simpa [h] using h3
    linarith
  exact this
