import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Pow

open Nat

theorem rmo_2000_2
  (x y : ℕ)
  (hx : 0 < x)
  (hy : 0 < y)
  (h : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8) :
  x = 9 ∧ y = 11 := by
  by_cases h9 : x = 9
  · -- the solution x = 9
    have hx9 : x = 9 := h9
    have : y ^ 3 = 9 ^ 3 + 8 * 9 ^ 2 - 6 * 9 + 8 := by
      simpa [hx9] using h
    norm_num at this
    have hy_eq : y ^ 3 = 11 ^ 3 := by
      simpa using this
    have inj : Function.Injective fun n : ℕ => n ^ 3 :=
      pow_left_injective (Nat.succ_pos 2)
    have hy11 : y = 11 := inj hy_eq
    exact ⟨by simpa [hx9], hy11⟩
  · -- x ≠ 9
    have hneq : x ≠ 9 := h9
    have hlt_or_gt : x < 9 ∨ 9 < x := lt_or_gt_of_ne hneq
    cases hlt_or_gt with
    | inl hlt =>
        --  x < 9
        have h1 : (x + 1) ^ 3 < x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := by
          have hxpos : 0 < x := hx
          have : (x + 1) ^ 3 < x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := by
            nlinarith
          exact this
        have h2 : x ^ 3 + 8 * x ^ 2 - 6 * x + 8 < (x + 2) ^ 3 := by
          have hxpos : 0 < x := hx
          have : x ^ 3 + 8 * x ^ 2 - 6 * x + 8 < (x + 2) ^ 3 := by
            nlinarith
          exact this
        have h1' : (x + 1) ^ 3 < y ^ 3 := by
          simpa [h] using h1
        have h2' : y ^ 3 < (x + 2) ^ 3 := by
          simpa [h] using h2
        have hlow : x + 1 < y :=
          Nat.lt_of_pow_lt_pow (by decide : 0 < 3) h1'
        have hhigh : y < x + 2 :=
          Nat.lt_of_pow_lt_pow (by decide : 0 < 3) h2'
        have : y ≤ x + 1 := (Nat.lt_succ_iff).mp hhigh
        have : (x + 1) < (x + 1) :=
          Nat.lt_of_lt_of_le hlow this
        exact (Nat.lt_irrefl _ this).elim
    | inr hgt =>
        -- 9 < x
        have h1 : (x + 2) ^ 3 < x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := by
          have hxpos : 0 < x := hx
          have : (x + 2) ^ 3 < x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := by
            nlinarith
          exact this
        have h2 : x ^ 3 + 8 * x ^ 2 - 6 * x + 8 < (x + 3) ^ 3 := by
          have hxpos : 0 < x := hx
          have : x ^ 3 + 8 * x ^ 2 - 6 * x + 8 < (x + 3) ^ 3 := by
            nlinarith
          exact this
        have h1' : (x + 2) ^ 3 < y ^ 3 := by
          simpa [h] using h1
        have h2' : y ^ 3 < (x + 3) ^ 3 := by
          simpa [h] using h2
        have hlow : x + 2 < y :=
          Nat.lt_of_pow_lt_pow (by decide : 0 < 3) h1'
        have hhigh : y < x + 3 :=
          Nat.lt_of_pow_lt_pow (by decide : 0 < 3) h2'
        have : y ≤ x + 2 := (Nat.lt_succ_iff).mp hhigh
        have : (x + 2) < (x + 2) :=
          Nat.lt_of_lt_of_le hlow this
        exact (Nat.lt_irrefl _ this).elim
