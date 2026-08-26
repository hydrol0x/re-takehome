import Mathlib

lemma h04_algebraic_equiv (x y : ℕ) :
    x ^ 2 = y ^ 2 + 2 * y + 17 ↔ x ^ 2 = (y + 1) ^ 2 + 16 := by ring

lemma h04_strict_order (x y : ℕ) (h : x ^ 2 = (y + 1) ^ 2 + 16) :
    x > y + 1 := by nlinarith

lemma h04_diff_squares (x y : ℕ) (h_order : x > y + 1) (h_sq : x ^ 2 = (y + 1) ^ 2 + 16) :
    (x - (y + 1)) * (x + (y + 1)) = 16 := by sorry

lemma h04_even_factor (x y : ℕ) (h_order : x > y + 1) (h_sq : x ^ 2 = (y + 1) ^ 2 + 16) :
    2 ∣ (x - (y + 1)) := by sorry

lemma h04_factor_bound (x y : ℕ) (h_order : x > y + 1) (h_sq : x ^ 2 = (y + 1) ^ 2 + 16) :
    x - (y + 1) ≤ 4 := by sorry

lemma h04_exact_factor (x y : ℕ) (h_order : x > y + 1) (h_sq : x ^ 2 = (y + 1) ^ 2 + 16) :
    x - (y + 1) = 2 := by sorry

lemma h04_solve_vars (x y : ℕ) (h_fact : x - (y + 1) = 2) (h_order : x > y + 1) :
    x = 5 ∧ y = 2 := by sorry

theorem h04_square_shift (x y : ℕ) (hx : 0 < x) (hy : 0 < y) :
    x ^ 2 = y ^ 2 + 2 * y + 17 ↔ x = 5 ∧ y = 2 := by sorry
