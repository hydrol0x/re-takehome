import Mathlib.Tactic

lemma h04_sq_comp (x y : ℕ) : x ^ 2 = y ^ 2 + 2 * y + 17 ↔ x ^ 2 = (y + 1) ^ 2 + 16 := by ring

lemma h04_x_gt (x y : ℕ) (h : x ^ 2 = y ^ 2 + 2 * y + 17) : x > y + 1 := by nlinarith

lemma h04_diff_sq (x y : ℕ) (h : x > y + 1) :
    (x - (y + 1)) * (x + (y + 1)) = x ^ 2 - (y + 1) ^ 2 := by simp [Nat.sq_sub_sq, Nat.mul_comm]

lemma h04_prod_16 (x y : ℕ) (h : x ^ 2 = y ^ 2 + 2 * y + 17) :
    (x - (y + 1)) * (x + (y + 1)) = 16 := by sorry

lemma h04_sum_ge_4 (x y : ℕ) (h : x ^ 2 = y ^ 2 + 2 * y + 17) :
    x + (y + 1) ≥ 4 := by nlinarith

lemma h04_diff_le_4 (x y : ℕ) (h : x ^ 2 = y ^ 2 + 2 * y + 17) :
    x - (y + 1) ≤ 4 := by sorry

lemma h04_diff_ge_1 (x y : ℕ) (h : x > y + 1) :
    x - (y + 1) ≥ 1 := by omega

lemma h04_unique_factor (x y : ℕ) (h : x ^ 2 = y ^ 2 + 2 * y + 17) :
    x - (y + 1) = 2 := by sorry

lemma h04_solve (x y : ℕ) (h : x ^ 2 = y ^ 2 + 2 * y + 17) :
    x = 5 ∧ y = 2 := by sorry

theorem h04_square_shift (x y : ℕ) (hx : 0 < x) (hy : 0 < y) :
    x ^ 2 = y ^ 2 + 2 * y + 17 ↔ x = 5 ∧ y = 2 := by sorry
