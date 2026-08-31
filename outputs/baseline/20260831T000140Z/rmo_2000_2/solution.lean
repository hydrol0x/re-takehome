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
  -- rewrite the equation
  have h₁ : y ^ 3 = (x + 2) ^ 3 - 2 * x * (9 - x) := by
    have : x ^ 3 + 8 * x ^ 2 - 6 * x + 8 =
        (x + 2) ^ 3 - 2 * x * (9 - x) := by
      ring
    simpa [this] using h
  -- split on whether x ≤ 9 or 9 < x
  rcases le_or_gt x 9 with hle | hgt
  · -- case `x ≤ 9`
    have hle' : y ^ 3 ≤ (x + 2) ^ 3 := by
      have : (x + 2) ^ 3 - 2 * x * (9 - x) ≤ (x + 2) ^ 3 := by
        have : 0 ≤ 2 * x * (9 - x) := Nat.zero_le _
        exact sub_le_iff_le_add'.mpr (by
          have := Nat.le_add_left (2 * x * (9 - x)) ((x + 2) ^ 3)
          simpa [add_comm] using this)
      exact le_of_eq_of_le h₁ this
    have hpos : 0 < 5 * x ^ 2 - 9 * x + 7 := by
      nlinarith
    have hygt : (x + 1) ^ 3 < y ^ 3 := by
      have : (x + 1) ^ 3 + (5 * x ^ 2 - 9 * x + 7) = y ^ 3 := by
        have : y ^ 3 = (x + 1) ^ 3 + (5 * x ^ 2 - 9 * x + 7) := by
          have : x ^ 3 + 8 * x ^ 2 - 6 * x + 8 =
              (x + 1) ^ 3 + (5 * x ^ 2 - 9 * x + 7) := by ring
          simpa [h] using this
        symm
        exact this
      have : (x + 1) ^ 3 < (x + 1) ^ 3 + (5 * x ^ 2 - 9 * x + 7) :=
        Nat.lt_add_of_pos_right _ hpos
      simpa [this] using this
    have hylt : y ≤ x + 2 := by
      have : y ^ 3 ≤ (x + 2) ^ 3 := hle'
      exact Nat.le_of_pow_le_pow this (by decide) (by decide)
    have hygt' : x + 1 < y := by
      have : (x + 1) ^ 3 < y ^ 3 := hygt
      exact Nat.lt_of_pow_lt_pow this (by decide) (by decide)
    have hyge : x + 2 ≤ y := Nat.succ_le_of_lt hygt'
    have hy_eq : y = x + 2 := le_antisymm hylt hyge
    -- plug back to get x = 9
    have : (x + 2) ^ 3 = (x + 2) ^ 3 - 2 * x * (9 - x) := by
      simpa [hy_eq] using h₁
    have hzero : 2 * x * (9 - x) = 0 := by
      have : (x + 2) ^ 3 - ((x + 2) ^ 3 - 2 * x * (9 - x)) = 0 := by
        simpa [sub_eq, add_comm, add_left_comm, add_assoc] using congrArg (fun t => (x + 2) ^ 3 - t) this
      simpa [sub_sub, sub_self] using this
    have hxpos : x ≠ 0 := ne_of_gt hx
    have h2pos : (2 : ℕ) ≠ 0 := by decide
    have : x = 0 ∨ 9 - x = 0 := by
      have : 2 * x * (9 - x) = 0 := hzero
      have := Nat.mul_eq_zero.mp (Nat.mul_eq_zero.mp (Nat.mul_eq_zero.mp this).resolve_left h2pos).resolve_left hxpos
      exact this
    have hx9 : x = 9 := by
      cases this with
      | inl h0 => exact (hxpos h0).elim
      | inr hsub =>
        have : 9 ≤ x := by
          have : 9 - x = 0 := hsub
          have : x ≤ 9 := hle
          exact le_antisymm this hsub
        exact le_antisymm hle this
    exact ⟨hx9, by simpa [hy_eq, hx9]⟩
  · -- case `9 < x`
    have hgt' : 9 ≤ x.succ := Nat.succ_le_of_lt hgt
    have hpos : 0 < 2 * x * (9 - x) := by
      have : 9 - x = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt hgt)
      simpa [this] using Nat.zero_lt_one
    have hlt : (x + 2) ^ 3 < y ^ 3 := by
      have : (x + 2) ^ 3 = y ^ 3 + 2 * x * (9 - x) := by
        have := h₁
        have : y ^ 3 + 2 * x * (9 - x) = (x + 2) ^ 3 := by
          simpa [add_comm, add_left_comm, add_assoc] using this.symm
        simpa using this.symm
      have : (x + 2) ^ 3 ≤ y ^ 3 := le_of_eq_of_le this (Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) (???)
