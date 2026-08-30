import Mathlib

/-- Positive reals `a, b, c` with `a + b + c = 3` satisfy `a*b + b*c + c*a ≤ 3`. -/
theorem p08_sum_products (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 3) : a * b + b * c + c * a ≤ 3 := by
  -- non‑negativity of the variables
  have hna : (0 : ℝ) ≤ a := le_of_lt ha
  have hnb : (0 : ℝ) ≤ b := le_of_lt hb
  have hnc : (0 : ℝ) ≤ c := le_of_lt hc
  -- a² + b² + c² ≥ ab + bc + ca
  have hsq : a ^ 2 + b ^ 2 + c ^ 2 ≥ a * b + b * c + c * a := by
    nlinarith
  -- expand (a+b+c)²
  have hsum_sq : (a + b + c) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a * b + b * c + c * a) := by
    ring
  -- deduce 3·(ab+bc+ca) ≤ (a+b+c)²
  have h_three_mul : 3 * (a * b + b * c + c * a) ≤ (a + b + c) ^ 2 := by
    have : a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a * b + b * c + c * a) ≥
        3 * (a * b + b * c + c * a) := by
      linarith
    simpa [hsum_sq] using this
  -- replace a+b+c by 3
  have h_three_mul' : 3 * (a * b + b * c + c * a) ≤ 9 := by
    simpa [h] using h_three_mul
  -- divide by the positive number 3
  have : a * b + b * c + c * a ≤ 3 := by
    have hpos : (0 : ℝ) < (3 : ℝ) := by norm_num
    linarith
  exact this
