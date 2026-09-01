import Mathlib

/-- AM–GM for three factors: positive reals `a, b, c` satisfy
`8 * (a * b * c) ≤ (a + b) * (b + c) * (c + a)`. -/
theorem m08_amgm8 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    8 * (a * b * c) ≤ (a + b) * (b + c) * (c + a) := by
  -- rewrite the difference as a sum of non‑negative terms
  have h_eq :
      (a + b) * (b + c) * (c + a) - 8 * (a * b * c) =
        a * (b - c) ^ 2 + b * (c - a) ^ 2 + c * (a - b) ^ 2 := by
    ring
  -- each term on the right‑hand side is non‑negative
  have h_nonneg :
      0 ≤ a * (b - c) ^ 2 + b * (c - a) ^ 2 + c * (a - b) ^ 2 := by
    have ha0 : (0 : ℝ) ≤ a := le_of_lt ha
    have hb0 : (0 : ℝ) ≤ b := le_of_lt hb
    have hc0 : (0 : ℝ) ≤ c := le_of_lt hc
    have hsq1 : (0 : ℝ) ≤ (b - c) ^ 2 := by
      have : (0 : ℝ) ≤ (b - c) * (b - c) := mul_self_nonneg (b - c)
      simpa [pow_two] using this
    have hsq2 : (0 : ℝ) ≤ (c - a) ^ 2 := by
      have : (0 : ℝ) ≤ (c - a) * (c - a) := mul_self_nonneg (c - a)
      simpa [pow_two] using this
    have hsq3 : (0 : ℝ) ≤ (a - b) ^ 2 := by
      have : (0 : ℝ) ≤ (a - b) * (a - b) := mul_self_nonneg (a - b)
      simpa [pow_two] using this
    have hterm1 : (0 : ℝ) ≤ a * (b - c) ^ 2 := mul_nonneg ha0 hsq1
    have hterm2 : (0 : ℝ) ≤ b * (c - a) ^ 2 := mul_nonneg hb0 hsq2
    have hterm3 : (0 : ℝ) ≤ c * (a - b) ^ 2 := mul_nonneg hc0 hsq3
    exact add_nonneg (add_nonneg hterm1 hterm2) hterm3
  -- from the non‑negativity of the difference we obtain the desired inequality
  have hge : 0 ≤ (a + b) * (b + c) * (c + a) - 8 * (a * b * c) := by
    simpa [h_eq] using h_nonneg
  linarith
