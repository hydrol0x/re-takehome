import Mathlib

theorem h04_square_shift (x y : ℕ) (hx : 0 < x) (hy : 0 < y) :
    x ^ 2 = y ^ 2 + 2 * y + 17 ↔ x = 5 ∧ y = 2 := by
  constructor
  · intro h
    -- sandwich: (y+1)² < x² ≤ (y+5)², so y+2 ≤ x ≤ y+5
    have hlow : y + 1 < x := by
      rcases Nat.lt_or_ge (y + 1) x with h' | h'
      · exact h'
      · exfalso
        have h2 : x ^ 2 ≤ (y + 1) ^ 2 := Nat.pow_le_pow_left h' 2
        nlinarith [h, h2]
    have hhigh : x ≤ y + 5 := by
      rcases Nat.lt_or_ge (y + 5) x with h' | h'
      · exfalso
        have h2 : (y + 6) ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left (by omega) 2
        nlinarith [h, h2]
      · exact h'
    have hcase : x = y + 2 ∨ x = y + 3 ∨ x = y + 4 ∨ x = y + 5 := by omega
    rcases hcase with rfl | rfl | rfl | rfl
    · exfalso
      have h2 : 2 * y = 13 := by nlinarith [h]
      omega
    · have hy2 : y = 2 := by nlinarith [h]
      subst hy2
      exact ⟨rfl, rfl⟩
    · exfalso
      have h2 : 6 * y = 1 := by nlinarith [h]
      omega
    · exfalso
      have h2 : 8 * y + 8 = 0 := by nlinarith [h]
      omega
  · rintro ⟨rfl, rfl⟩
    norm_num
