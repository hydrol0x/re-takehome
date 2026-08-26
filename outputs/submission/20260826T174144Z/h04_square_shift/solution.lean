import Mathlib

theorem h04_square_shift (x y : ℕ) (hx : 0 < x) (hy : 0 < y) :
    x ^ 2 = y ^ 2 + 2 * y + 17 ↔ x = 5 ∧ y = 2 := by
  have h_main : ∀ (x y : ℕ), 0 < x → 0 < y → (x ^ 2 = y ^ 2 + 2 * y + 17 ↔ x = 5 ∧ y = 2) := by
    sorry
  exact h_main x y hx hy
