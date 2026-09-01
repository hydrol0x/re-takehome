import Mathlib

/-- AM–GM for three factors: positive reals `a, b, c` satisfy
`8 * (a * b * c) ≤ (a + b) * (b + c) * (c + a)`. -/
theorem m08_amgm8 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    8 * (a * b * c) ≤ (a + b) * (b + c) * (c + a) := by
  -- rewrite the difference as a sum of squares
  have h_eq :
      (a + b) * (b + c) * (c + a) - 8 * (a * b * c) =
        a * (b - c) ^ 2 + b * (c - a) ^ 2 + c * (a - b) ^ 2 := by
    ring
  -- each term in the sum of squares is non‑negative
  have h_nonneg :
      0 ≤ a * (b - c) ^ 2 + b * (c - a) ^ 2 + c * (a - b) ^ 2 := by
    have h1 : 0 ≤ a * (b - c) ^ 2 :=
      mul_nonneg (le_of_lt ha) (pow_two_nonneg (b - c))
    have h2 : 0 ≤ b * (c - a) ^ 2 :=
      mul_nonneg (le_of_lt hb) (pow_two_nonneg (c - a))
    have h3 : 0 ≤ c * (a - b) ^ 2 :=
      mul_nonneg (le_of_lt hc) (pow_two_nonneg (a - b))
    exact add_nonneg (add_nonneg h1 h2) h3
  -- therefore the original difference is non‑negative
  have h0 :
      0 ≤ (a + b) * (b + c) * (c + a) - 8 * (a * b * c) := by
    simpa [h_eq] using h_nonneg
  -- turn the non‑negativity of the difference into the desired inequality
  exact (sub_nonneg.mp h0)
