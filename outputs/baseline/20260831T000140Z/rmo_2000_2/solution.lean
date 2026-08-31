import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Nat

theorem rmo_2000_2
  (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
  (h : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8) :
  x = 9 ∧ y = 11 := by
  -- rewrite the equation in two convenient forms
  have h₁ : y ^ 3 = (x + 1) ^ 3 + (5 * x ^ 2 - 9 * x + 7) := by
    have := h
    ring_nf at this
    exact this
  have h₂ : y ^ 3 + 2 * x * (9 - x) = (x + 2) ^ 3 := by
    have := h
    ring_nf at this
    -- the right‑hand side becomes `x ^ 3 + 8 * x ^ 2 - 6 * x + 8 + 2 * x * (9 - x)`
    -- which simplifies to `(x + 2) ^ 3`
    ring
  -- the term added to `(x+1)^3` is always positive
  have hpos₁ : 0 < 5 * x ^ 2 - 9 * x + 7 := by
    have : (5 * (x : ℤ) ^ 2 - 9 * (x : ℤ) + 7) > 0 := by
      nlinarith [hx]
    exact_mod_cast this
  have hlt₁ : (x + 1) ^ 3 < y ^ 3 := by
    have := Nat.lt_add_of_pos_right ((x + 1) ^ 3) hpos₁
    simpa [h₁] using this
  by_cases hx9 : x = 9
  · -- the special case `x = 9`
    subst hx9
    have : y ^ 3 = 11 ^ 3 := by
      simpa using h
    have hy : y = 11 :=
      (Nat.pow_left_injective (by decide : 0 < (3 : ℕ))) this
    exact ⟨rfl, hy⟩
  · -- now `x ≠ 9`
    have hlt_or_gt : x < 9 ∨ 9 < x := lt_or_gt_of_ne hx9
    cases hlt_or_gt with
    | inl hlt9 =>
        -- `x < 9` : then `y^3 < (x+2)^3`
        have hpos₂ : 0 < 2 * x * (9 - x) := by
          have hxpos : 0 < x := hx
          have h9xpos : 0 < 9 - x := Nat.sub_pos_of_lt hlt9
          exact mul_pos (mul_pos (by decide) hxpos) h9xpos
        have hlt₂ : y ^ 3 < (x + 2) ^ 3 := by
          have := Nat.lt_add_of_pos_right (y ^ 3) hpos₂
          simpa [h₂] using this
        have hy_le : y ≤ x + 1 := (Nat.lt_succ_iff).mp hlt₂
        have hy_gt : x + 1 < y :=
          Nat.lt_of_pow_lt_pow (by
            have := hlt₁
            simpa [pow_three] using this) (by decide : 0 < (3 : ℕ))
        have : x + 1 < x + 1 := Nat.lt_of_lt_of_le hy_gt hy_le
        exact (lt_irrefl _ this).elim
    | inr hgt9 =>
        -- `9 < x` : then `(x+2)^3 < y^3 < (x+3)^3`
        have hpos₂ : 0 < 2 * x * (x - 9) := by
          have hxpos : 0 < x := hx
          have hx9pos : 0 < x - 9 := Nat.sub_pos_of_lt hgt9
          exact mul_pos (mul_pos (by decide) hxpos) hx9pos
        have hlt₁' : (x + 2) ^ 3 < y ^ 3 := by
          have := Nat.lt_add_of_pos_right ((x + 2) ^ 3) hpos₂
          -- from `y^3 = (x+2)^3 + 2*x*(x-9)`
          have h_eq : y ^ 3 = (x + 2) ^ 3 + 2 * x * (x - 9) := by
            have := h
            ring_nf at this
            -- rewrite `2 * x * (9 - x)` as `- 2 * x * (x - 9)`
            have : 2 * x * (9 - x) = -(2 * x * (x - 9)) := by
              ring
            simpa [this, add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using this
          simpa [h_eq] using this
        have hpos₃ : 0 < x ^ 2 + 33 * x + 19 := by
          have : (x : ℤ) ^ 2 + 33 * (x : ℤ) + 19 > 0 := by nlinarith [hx]
          exact_mod_cast this
        have hlt₃ : y ^ 3 < (x + 3) ^ 3 := by
          have : y ^ 3 + (x ^ 2 + 33 * x + 19) = (x + 3) ^ 3 := by
            have := h
            ring_nf at this
            ring
          have := Nat.lt_add_of_pos_right (y ^ 3) hpos₃
          simpa [this] using this
        have hy_le : y ≤ x + 2 := (Nat.lt_succ_iff).mp hlt₃
        have hy_gt : x + 2 < y :=
          Nat.lt_of_pow_lt_pow (by
            have := hlt₁'
            simpa [pow_three] using this) (by decide : 0 < (3 : ℕ))
        have : x + 2 < x + 2 := Nat.lt_of_lt_of_le hy_gt hy_le
        exact (lt_irrefl _ this).elim
