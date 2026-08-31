import Mathlib

-- Helper lemmas for putnam_2018_a1

lemma eq_3_over_2018_iff (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    ((1 : ℚ) / a + (1 : ℚ) / b = (3 : ℚ) / 2018) ↔
    3 * a * b = 2018 * (a + b) := by sorry

lemma transform_to_factored_form (a b : ℤ) (h : 3 * a * b = 2018 * (a + b)) :
    (3 * a - 2018) * (3 * b - 2018) = 2018 ^ 2 := by linarith

lemma bound_on_a (a b : ℤ) (ha : 0 < a) (hb : 0 < b) (h : 3 * a * b = 2018 * (a + b)) :
    a ≤ 1345 := by sorry

lemma divisor_of_2018_sq (n : ℤ) (h : n ∣ (2018 : ℤ) ^ 2) :
    n = 1 ∨ n = 2 ∨ n = 2018 ∨ n = 4036 ∨ n = 1009 ∨ n = 2018 ∨ n = 2036164 ∨ n = 4072328 ∨ n = 1009 * 2018 ∨ n = 2018 ^ 2 := by sorry

lemma solve_for_a (d : ℤ) (hd : d ∣ (2018 : ℤ) ^ 2) :
    3 * a - 2018 = d → a = (d + 2018) / 3 := by omega

lemma check_valid_pair (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    ((1 : ℚ) / a + (1 : ℚ) / b = (3 : ℚ) / 2018) →
    (⟨a, b⟩ ∈ ({(673, 1358114), (674, 340033), (1009, 2018),
      (2018, 1009), (340033, 674), (1358114, 673)} : Set (ℤ × ℤ))) := by sorry

theorem putnam_2018_a1
  (a b : ℤ)
  (h : 0 < a ∧ 0 < b) :
  ((1 : ℚ) / a + (1 : ℚ) / b = (3 : ℚ) / 2018) ↔
    (⟨a, b⟩ ∈ ({(673, 1358114), (674, 340033), (1009, 2018),
      (2018, 1009), (340033, 674), (1358114, 673)} : Set (ℤ × ℤ))) := by sorry
