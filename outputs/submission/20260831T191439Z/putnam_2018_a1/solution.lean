import Mathlib

set_option maxHeartbeats 1000000

lemma rational_to_integer {a b : ℤ} (ha : 0 < a) (hb : 0 < b) :
  (1 : ℚ) / a + (1 : ℚ) / b = (3 : ℚ) / 2018 ↔
  (3 * a - 2018) * (3 * b - 2018) = 2018 ^ 2 := by sorry

lemma char_solutions {a b : ℤ} (ha : 0 < a) (hb : 0 < b) :
  (3 * a - 2018) * (3 * b - 2018) = 2018 ^ 2 ↔
  (⟨a, b⟩ ∈ ({(673, 1358114), (674, 340033), (1009, 2018),
    (2018, 1009), (340033, 674), (1358114, 673)} : Set (ℤ × ℤ))) := by sorry

theorem putnam_2018_a1
  (a b : ℤ)
  (h : 0 < a ∧ 0 < b) :
  ((1 : ℚ) / a + (1 : ℚ) / b = (3 : ℚ) / 2018) ↔
    (⟨a, b⟩ ∈ ({(673, 1358114), (674, 340033), (1009, 2018),
      (2018, 1009), (340033, 674), (1358114, 673)} : Set (ℤ × ℤ))) := by
  rw [rational_to_integer h.left h.right]
  rw [char_solutions h.left h.right]
