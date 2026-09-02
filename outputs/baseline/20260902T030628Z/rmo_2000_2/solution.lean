import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

open Nat

theorem rmo_2000_2
  (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
  (h : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8) :
  x = 9 ∧ y = 11 := by
  have h_cases : x < 9 ∨ x = 9 ∨ 9 < x := by
    have := lt_or_ge x 9
    cases this with
    | inl hlt => exact Or.inl hlt
    | inr hge =>
        have h' := lt_or_eq_of_le hge
        cases h' with
        | inl hgt => exact Or.inr <| Or.inr hgt
        | inr heq => exact Or.inr <| Or.inl heq
  rcases h_cases with hlt | h_eq | hgt
  · -- case `x < 9`
    have hpos9x : 0 < 9 - x := Nat.sub_pos_of_lt hlt
    -- y³ < (x+2)³
    have hlt' : y ^ 3 < (x + 2) ^ 3 := by
      have : (x + 2) ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8 + 2 * x * (9 - x) := by
        ring
      have : (x + 2) ^ 3 - y ^ 3 = 2 * x * (9 - x) := by
        simpa [h, this] using rfl
      have hpos : 0 < 2 * x * (9 - x) := by
        have hxpos : 0 < x := hx
        have h9pos : 0 < 9 - x := hpos9x
        have : 0 < (2 : ℕ) := by decide
        exact Nat.mul_pos (Nat.mul_pos this hxpos) h9pos
      have : (x + 2) ^ 3 - y ^ 3 > 0 := by
        simpa [this] using hpos
      exact Nat.sub_pos_iff_lt.mp this
    -- (x+1)³ < y³
    have hgt' : (x + 1) ^ 3 < y ^ 3 := by
      have : x ^ 3 + 8 * x ^ 2 - 6 * x + 8 =
          (x + 1) ^ 3 + (5 * x ^ 2 - 9 * x + 7) := by ring
      have hpos : 0 < 5 * x ^ 2 - 9 * x + 7 := by
        have : (5 : ℤ) * (x : ℤ) ^ 2 - 9 * (x : ℤ) + 7 > 0 := by
          nlinarith [hx]
        exact_mod_cast this
      have : y ^ 3 = (x + 1) ^ 3 + (5 * x ^ 2 - 9 * x + 7) := by
        simpa [h, this] using rfl
      have : (x + 1) ^ 3 < (x + 1) ^ 3 + (5 * x ^ 2 - 9 * x + 7) :=
        Nat.lt_add_of_pos_right _ hpos
      simpa [this] using this
    have hy_gt : x + 1 < y :=
      ((strictMono_pow (Nat.succ_pos 2)).lt_iff_lt).1 hgt'
    have hy_lt : y < x + 2 :=
      ((strictMono_pow (Nat.succ_pos 2)).lt_iff_lt).1 hlt'
    have : (x + 1) < x + 2 := Nat.lt_succ_self (x + 1)
    have : False := Nat.not_lt_of_ge (Nat.le_of_lt hy_lt) hy_gt
    exact (False.elim this)
  · -- case `x = 9`
    subst h_eq
    have hval : y ^ 3 = 1331 := by
      norm_num at h
      simpa using h
    have h10 : (10 : ℕ) ^ 3 < y ^ 3 := by
      norm_num at hval
      have : (10 : ℕ) ^ 3 = 1000 := by norm_num
      have : (10 : ℕ) ^ 3 < 1331 := by norm_num
      simpa [hval] using this
    have hy_ge11 : 11 ≤ y :=
      (Nat.succ_le_iff).2 ((strictMono_pow (Nat.succ_pos 2)).lt_iff_lt).1 h10
    have h12 : y ^ 3 < (12 : ℕ) ^ 3 := by
      norm_num at hval
      have : (12 : ℕ) ^ 3 = 1728 := by norm_num
      have : 1331 < (12 : ℕ) ^ 3 := by norm_num
      simpa [hval] using this
    have hy_le11 : y ≤ 11 :=
      (Nat.lt_succ_iff).1 ((strictMono_pow (Nat.succ_pos 2)).lt_iff_lt).2 h12
    have hy_eq : y = 11 := le_antisymm hy_le11 hy_ge11
    exact ⟨rfl, hy_eq⟩
  · -- case `9 < x`
    have hposx9 : 0 < x - 9 := Nat.sub_pos_of_lt hgt
    -- (x+2)³ < y³
    have hlt' : (x + 2) ^ 3 < y ^ 3 := by
      have : (x + 2) ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8 - 2 * x * (x - 9) := by
        ring
      have : y ^ 3 - (x + 2) ^ 3 = 2 * x * (x - 9) := by
        simpa [h, this] using rfl
      have hpos : 0 < 2 * x * (x - 9) := by
        have hxpos : 0 < x := hx
        have h9pos : 0 < x - 9 := hposx9
        have : 0 < (2 : ℕ) := by decide
        exact Nat.mul_pos (Nat.mul_pos this hxpos) h9pos
      have : y ^ 3 - (x + 2) ^ 3 > 0 := by
        simpa [this] using hpos
      exact Nat.sub_pos_iff_lt.mp this
    -- y³ < (x+3)³
    have hgt' : y ^ 3 < (x + 3) ^ 3 := by
      have : (x + 3) ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8 + (x ^ 2 + 33 * x + 19) := by
        ring
      have hpos : 0 < x ^ 2 + 33 * x + 19 := by
        have : (x : ℤ) ^ 2 + 33 * (x : ℤ) + 19 > 0 := by nlinarith
        exact_mod_cast this
      have : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := h
      have : y ^ 3 < (x + 3) ^ 3 := by
        have : y ^ 3 < x ^ 3 + 8 * x ^ 2 - 6 * x + 8 + (x ^ 2 + 33 * x + 19) :=
          Nat.lt_add_of_pos_right _ hpos
        simpa [this] using this
      simpa [this] using this
    have hy_gt : x + 2 < y :=
      ((strictMono_pow (Nat.succ_pos 2)).lt_iff_lt).1 hlt'
    have hy_lt : y < x + 3 :=
      ((strictMono_pow (Nat.succ_pos 2)).lt_iff_lt).1 hgt'
    have : (x + 2) < x + 3 := Nat.lt_succ_self (x + 2)
    have : False := Nat.not_lt_of_ge (Nat.le_of_lt hy_lt) hy_gt
    exact (False.elim this)
