import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Order.Ring.Defs

theorem rmo_2000_2
  (x y : ℕ)
  (hx : 0 < x)
  (hy : 0 < y)
  (h : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8) :
  x = 9 ∧ y = 11 := by
  have h_main : x ≤ 9 := by
    by_contra! hx'
    have h_ge : x ≥ 10 := by omega
    have h1 : (x + 2) ^ 3 < y ^ 3 := by
      calc
        (x + 2) ^ 3 = x ^ 3 + 6 * x ^ 2 + 12 * x + 8 := by ring
        _ < x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := by
          have : 0 < 2 * x ^ 2 - 18 * x := by
            have : x ≥ 10 := h_ge
            nlinarith
          omega
        _ = y ^ 3 := by rw [h]
    have h2 : y ^ 3 < (x + 3) ^ 3 := by
      calc
        y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := by rw [h]
        _ < x ^ 3 + 9 * x ^ 2 + 27 * x + 27 := by
          have : 0 < x ^ 2 + 33 * x + 19 := by
            have : x ≥ 10 := h_ge
            nlinarith
          omega
        _ = (x + 3) ^ 3 := by ring
    have h3 : x + 2 < y := Nat.lt_of_lt_of_le (by exact_mod_cast h1) (by omega)
    have h4 : y < x + 3 := Nat.lt_of_lt_of_le (by exact_mod_cast h2) (by omega)
    omega
  interval_cases x <;> norm_num at h ⊢ <;>
    (try omega) <;>
    (try {
      have : y ≤ 15 := by
        nlinarith [pow_pos hy 3]
      interval_cases y <;> norm_num at h ⊢ <;> omega
    })
