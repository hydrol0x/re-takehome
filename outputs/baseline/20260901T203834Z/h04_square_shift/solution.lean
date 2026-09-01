import Mathlib.Tactic
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Nat.Factor

open Nat

theorem h04_square_shift (x y : ℕ) (hx : 0 < x) (hy : 0 < y) :
    x ^ 2 = y ^ 2 + 2 * y + 17 ↔ x = 5 ∧ y = 2 := by
  constructor
  · intro h
    -- rewrite the equation as a difference of two squares
    have hdiff : x ^ 2 - (y + 1) ^ 2 = 16 := by
      have := congrArg (fun t : ℕ => t - (y + 1) ^ 2) (by
        simpa [pow_two, mul_comm, mul_left_comm, mul_assoc,
               two_mul, add_comm, add_left_comm, add_assoc] using h)
      simpa [Nat.add_sub_cancel] using this
    -- factor the left hand side
    have hprod : (x - (y + 1)) * (x + (y + 1)) = 16 := by
      calc
        (x - (y + 1)) * (x + (y + 1))
            = x ^ 2 - (y + 1) ^ 2 := by
              simpa [pow_two] using (Nat.mul_self_sub_mul_self_eq x (y + 1)).symm
        _ = 16 := hdiff
    -- positivity of the first factor
    have hpos : 0 < x - (y + 1) := by
      have : 0 < (x - (y + 1)) * (x + (y + 1)) := by
        have : (0 : ℕ) < 16 := by decide
        simpa [hprod] using this
      exact Nat.pos_of_mul_pos_left this (Nat.zero_lt_succ _)
    -- the first factor is at most 4
    have hle4 : x - (y + 1) ≤ 4 := by
      have : (x - (y + 1)) * (x - (y + 1)) ≤ (x - (y + 1)) * (x + (y + 1)) := by
        have : x - (y + 1) ≤ x + (y + 1) := by
          have : 0 ≤ y + 1 := Nat.zero_le _
          exact Nat.sub_le_iff_le_add'.mpr (Nat.le_add_left _ _)
        exact Nat.mul_le_mul_left _ this
      have : (x - (y + 1)) * (x - (y + 1)) ≤ 16 := by
        simpa [hprod] using this
      have : (x - (y + 1)) ≤ 4 := by
        -- a square ≤ 16 forces the number ≤ 4
        have hcases : (x - (y + 1)) ≤ 4 ∨ 5 ≤ x - (y + 1) := le_or_gt _ 4
        cases hcases with
        | inl h => exact h
        | inr hge5 =>
          have : 25 ≤ (x - (y + 1)) * (x - (y + 1)) :=
            Nat.mul_self_le_mul_self (Nat.succ_le_of_lt hge5)
          have : 25 ≤ 16 := le_trans this ‹_›
          exact (Nat.not_lt.mpr this).elim (by decide)
      exact this
    -- enumerate the possible values of the first factor
    have hcases : x - (y + 1) = 2 ∨ x - (y + 1) = 4 := by
      have : x - (y + 1) = 1 ∨ x - (y + 1) = 2 ∨ x - (y + 1) = 3 ∨ x - (y + 1) = 4 := by
        interval_cases (x - (y + 1)) using Nat with
        | zero => cases (Nat.not_lt.mpr (Nat.le_of_lt hpos) (by decide))
        | succ n =>
          have : n ≤ 3 := Nat.succ_le_iff.mp (Nat.le_of_lt_succ (by
            have : (x - (y + 1)) ≤ 4 := hle4
            exact this))
          interval_cases n using Nat with
          | zero => exact Or.inl rfl
          | succ n' =>
            have : n' ≤ 2 := Nat.succ_le_iff.mp (Nat.le_of_lt_succ (by
              have : n ≤ 3 := this
              exact this))
            interval_cases n' using Nat with
            | zero => exact Or.inr (Or.inl rfl)
            | succ n'' =>
              have : n'' ≤ 1 := Nat.succ_le_iff.mp (Nat.le_of_lt_succ (by
                have : n' ≤ 2 := this
                exact this))
              interval_cases n'' using Nat with
              | zero => exact Or.inr (Or.inr rfl)
              | succ n''' => cases (Nat.not_lt.mpr (Nat.succ_le_of_lt (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_s
