import Mathlib.Tactic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Pow

open Nat

/-- The Diophantine equation `y³ = x³ + 8x² - 6x + 8` has the unique solution
`(x , y) = (9 , 11)` in positive integers. -/
theorem rmo_2000_2
  (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
  (h : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8) :
  x = 9 ∧ y = 11 := by
  have hxpos : 0 < x := hx
  have hypos : 0 < y := hy
  -- rewrite the right‑hand side
  have h₁ : y ^ 3 = (x + 2) ^ 3 + 2 * x * (x - 9) := by
    have : (x + 2) ^ 3 + 2 * x * (x - 9) = x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := by
      ring
    simpa [this] using h
  -- split according to the size of `x`
  rcases lt_or_ge x 9 with hlt9 | hge9
  · -- `x ≤ 8`.  Then `y³` lies strictly between two consecutive cubes,
    -- which is impossible.
    have hxle8 : x ≤ 8 := (Nat.lt_succ_iff).mp hlt9
    have hlt_left : (x + 1) ^ 3 < y ^ 3 := by
      have : (x + 1) ^ 3 = x ^ 3 + 3 * x ^ 2 + 3 * x + 1 := by ring
      have : x ^ 3 + 3 * x ^ 2 + 3 * x + 1 < x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := by
        have : (5 : ℤ) * (x : ℤ) ^ 2 - 9 * (x : ℤ) + 7 > 0 := by
          have : (0 : ℤ) ≤ (5 : ℤ) * (x : ℤ) ^ 2 := by exact mul_nonneg (by decide) (pow_two_nonneg _)
          linarith
        exact_mod_cast this
      simpa [h] using this
    have hlt_right : y ^ 3 < (x + 2) ^ 3 := by
      have : y ^ 3 = (x + 2) ^ 3 - 2 * x * (9 - x) := by
        have : (x + 2) ^ 3 - 2 * x * (9 - x) = (x + 2) ^ 3 + 2 * x * (x - 9) := by
          ring
        simpa [h₁] using this
      have : (x + 2) ^ 3 - 2 * x * (9 - x) < (x + 2) ^ 3 := by
        have : 0 < 2 * x * (9 - x) := by
          have hxpos' : (0 : ℤ) < (x : ℤ) := by exact_mod_cast hxpos
          have h9x : (0 : ℤ) < 9 - (x : ℤ) := by
            have : (x : ℤ) ≤ 8 := by exact_mod_cast hxle8
            linarith
          have : (0 : ℤ) < (2 : ℤ) * (x : ℤ) * (9 - (x : ℤ)) := by nlinarith
          exact_mod_cast this
        have : (x + 2) ^ 3 - 2 * x * (9 - x) < (x + 2) ^ 3 := by
          have : (x + 2) ^ 3 - 2 * x * (9 - x) + 2 * x * (9 - x) = (x + 2) ^ 3 := by ring
          linarith
        exact this
      simpa [this] using this
    have hle1 : x + 1 ≤ y := by
      have : (x + 1) ^ 3 ≤ y ^ 3 := Nat.le_of_lt hlt_left
      exact (pow_le_iff_le_right (Nat.succ_pos _)).1 this
    have hle2 : y ≤ x + 2 := by
      have : y ^ 3 ≤ (x + 2) ^ 3 := Nat.le_of_lt hlt_right
      exact (pow_le_iff_le_right (Nat.succ_pos _)).1 this
    have hy_eq : y = x + 2 := le_antisymm hle2 (Nat.succ_le_of_lt hle1)
    have : y ^ 3 = (x + 2) ^ 3 := by simpa [hy_eq] using h
    have : (x + 2) ^ 3 < (x + 2) ^ 3 := by
      have : (x + 1) ^ 3 < (x + 2) ^ 3 := by
        have : (x + 1) ^ 3 < y ^ 3 := hlt_left
        simpa [hy_eq] using hlt_right
      exact lt_of_lt_of_le this (le_of_eq rfl)
    exact (lt_irrefl _ this).elim
  · -- `x ≥ 9`.  First treat the case `x = 9`.
    have h9 : 9 ≤ x := hge9
    rcases lt_or_eq_of_le h9 with hgt9 | rfl
    · -- `x > 9`.  Then `y³` lies strictly between two consecutive cubes,
      -- which is impossible.
      have hxgt9 : 9 < x := hgt9
      have hpos : 0 < 2 * x * (x - 9) := by
        have hxpos' : (0 : ℤ) < (x : ℤ) := by exact_mod_cast hxpos
        have hxx : (0 : ℤ) < (x : ℤ) - 9 := by
          have : (9 : ℤ) < (x : ℤ) := by exact_mod_cast hxgt9
          linarith
        have : (0 : ℤ) < (2 : ℤ) * (x : ℤ) * ((x : ℤ) - 9) := by nlinarith
        exact_mod_cast this
      have hlt_left : (x + 2) ^ 3 < y ^ 3 := by
        have : y ^ 3 = (x + 2) ^ 3 + 2 * x * (x - 9) := by
          simpa [h₁] using rfl
        have : (x + 2) ^ 3 < (x + 2) ^ 3 + 2 * x * (x - 9) := by
          have : 0 < 2 * x * (x - 9) := hpos
          have : (x + 2) ^ 3 + 0 < (x + 2) ^ 3 + 2 * x * (x - 9) := add_lt_add_left this _
          simpa using this
        simpa [this] using this
      have hlt_right : y ^ 3 < (x + 3) ^ 3 := by
        have : (x + 3) ^ 3 - y ^ 3 = (x + 3) ^ 3 - ((x + 2) ^ 3 + 2 * x * (x - 9)) := by
          simpa [h₁] using rfl
        have : (x + 3) ^ 3 - (x + 2) ^ 3 = 3 * x ^ 2 + 15 * x + 19 := by ring
        have : (x + 3) ^ 3 - y ^ 3 = (3 * x ^ 2 + 15 * x + 19) - 2 * x * (x - 9) := by
          simpa [this] using this
        have : 0 < (3 * x ^ 2 + 15 * x + 19) - 2 * x * (x - 9) := by
          have : (x : ℤ) ≥ 10 := by exact_mod_cast Nat.succ_le_of_lt hxgt9
          have : (0 : ℤ) < (x : ℤ) ^ 2 + 33 * (x : ℤ) + 19 := by nlinarith
          exact_mod_cast this
        have : (x + 3) ^ 3 - y ^ 3 > 0 := this
        have : y ^ 3 < (x + 3) ^ 3 := lt_of_sub_pos_right this
        exact this
      have hle1 : x + 2 ≤ y := by
        have : (x + 2) ^ 3 ≤ y ^ 3 := Nat.le_of_lt hlt_left
        exact (pow_le_iff_le_right (Nat.succ_pos _)).1 this
      have hle2 : y ≤ x + 3 := by
        have : y ^ 3 ≤ (x + 3) ^ 3 := Nat.le_of_lt hlt_right
        exact (pow_le_iff_le_right (Nat.succ_pos _)).1 this
      have hy_eq : y = x + 2 := le_antisymm hle2 (Nat.succ_le_of_lt hle1)
      have : y ^ 3 = (x + 2
