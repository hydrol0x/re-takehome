import Mathlib.Tactic
import Mathlib.Data.Nat.Cube

open Nat

/-- The cubic polynomial appearing in the statement. -/
def f (x : ℕ) : ℕ := x ^ 3 + 8 * x ^ 2 - 6 * x + 8

theorem rmo_2000_2
  (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
  (h : y ^ 3 = f x) :
  x = 9 ∧ y = 11 := by
  have hpos : 0 < f x := by
    have : 0 < 8 * x ^ 2 - 6 * x + 8 := by
      have hx' : (0 : ℤ) ≤ (x : ℤ) := by exact_mod_cast Nat.zero_le x
      have : (8 : ℤ) * (x : ℤ) ^ 2 - 6 * (x : ℤ) + 8 > (0 : ℤ) := by
        nlinarith
      exact_mod_cast this
    have : x ^ 3 < x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_of_lt this)
    exact Nat.lt_of_lt_of_le this (Nat.le_of_lt (Nat.succ_pos _))
  have hxlt : x < y := by
    have : x ^ 3 < y ^ 3 := by
      simpa [h] using lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_of_lt hpos)
    exact Nat.lt_of_pow_lt_pow this (by decide : 0 < (3 : ℕ))
  have hylt : y < x + 3 := by
    have : f x < (x + 3) ^ 3 := by
      have : ((f x : ℤ) : ℤ) < ((x + 3) ^ 3 : ℤ) := by
        zify
        have : (x : ℤ) ^ 3 + 8 * (x : ℤ) ^ 2 - 6 * (x : ℤ) + 8 -
                ((x + 3 : ℤ) ^ 3) = - (x : ℤ) ^ 2 - 33 * (x : ℤ) - 19 := by ring
        have : - (x : ℤ) ^ 2 - 33 * (x : ℤ) - 19 < 0 := by
          have : (x : ℤ) ^ 2 + 33 * (x : ℤ) + 19 > (0 : ℤ) := by nlinarith
          linarith
        have : (x : ℤ) ^ 3 + 8 * (x : ℤ) ^ 2 - 6 * (x : ℤ) + 8 <
                ((x + 3 : ℤ) ^ 3) := by
          have := sub_lt_0.mp (by
            simpa [this] using ‹- (x : ℤ) ^ 2 - 33 * (x : ℤ) - 19 < 0›)
          exact this
        exact_mod_cast this
      exact_mod_cast this
    have : y ^ 3 < (x + 3) ^ 3 := by
      simpa [h] using this
    exact Nat.lt_of_pow_lt_pow this (by decide : 0 < (3 : ℕ))
  have hy_range : y = x + 1 ∨ y = x + 2 := by
    have : x + 1 ≤ y ∧ y ≤ x + 2 := by
      exact ⟨Nat.succ_le_of_lt hxlt, Nat.le_of_lt_succ (Nat.succ_lt_of_lt hylt)⟩
    rcases this with ⟨h1, h2⟩
    have hcases : y = x + 1 ∨ y = x + 2 := by
      have : y ≤ x + 1 ∨ x + 1 < y := le_or_lt y (x + 1)
      cases this with
      | inl hle =>
          have : y = x + 1 := le_antisymm hle h1
          exact Or.inl this
      | inr hgt =>
          have : y ≤ x + 2 := h2
          have : y = x + 2 := le_antisymm hgt.le this
          exact Or.inr this
    exact hcases
  rcases hy_range with hcase | hcase
  · -- case y = x + 1, leads to a contradiction
    have : (x + 1) ^ 3 = f x := by
      simpa [hcase] using h
    have : (5 : ℤ) * (x : ℤ) ^ 2 - 9 * (x : ℤ) + 7 = 0 := by
      have : ((x + 1) ^ 3 : ℤ) - (f x : ℤ) = 0 := by
        simpa [this] using congrArg (fun t : ℕ => (t : ℤ)) this
      have : ((x : ℤ) ^ 3 + 3 * (x : ℤ) ^ 2 + 3 * (x : ℤ) + 1) -
              ((x : ℤ) ^ 3 + 8 * (x : ℤ) ^ 2 - 6 * (x : ℤ) + 8) = 0 := by
        simpa [pow_two, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm,
               add_assoc, sub_eq, sub_eq_add_neg] using this
      simpa [sub_eq, sub_eq_add_neg] using this
    have : (5 : ℤ) * (x : ℤ) ^ 2 - 9 * (x : ℤ) + 7 ≠ 0 := by
      have hxpos : (0 : ℤ) ≤ (x : ℤ) := by exact_mod_cast Nat.zero_le x
      have : (5 : ℤ) * (x : ℤ) ^ 2 - 9 * (x : ℤ) + 7 > 0 := by nlinarith
      exact ne_of_gt this
    exact (this.elim)
  · -- case y = x + 2
    have : (x + 2) ^ 3 = f x := by
      simpa [hcase] using h
    have : 2 * x * (x - 9) = 0 := by
      have : ((x + 2) ^ 3 : ℤ) - (f x : ℤ) = 0 := by
        simpa using congrArg (fun t : ℕ => (t : ℤ)) this
      have : ((x : ℤ) ^ 3 + 6 * (x : ℤ) ^ 2 + 12 * (x : ℤ) + 8) -
              ((x : ℤ) ^ 3 + 8 * (x : ℤ) ^ 2 - 6 * (x : ℤ) + 8) = 0 := by
        simpa [pow_two, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm,
               add_assoc, sub_eq, sub_eq_add_neg] using this
      simpa [sub_eq, sub_eq_add_neg] using this
    have hx9 : x = 9 := by
      have : 2 * x * (x - 9) = 0 := this
      have hxpos : 0 < x := hx
      have hxne : x ≠ 0 := Nat.ne_of_gt hxpos
      have h2pos : (2 : ℕ) ≠ 0 := by decide
      have : x * (x - 9) = 0 := by
        apply Nat.eq_of_mul_eq_mul_left (Nat.succ_ne_zero 1)
        simpa [h2pos] using this
      have hcases : x = 0 ∨ x - 9 = 0 := Nat.eq_zero_or_eq_zero_of_mul_eq_zero this
      cases hcases with
      | inl hzero => exact (hxne hzero).elim
      | inr hsub => 
          have : x = 9 := by
            have : x - 9 + 9 = x := Nat.sub_add_cancel (Nat.le_of_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_one))))))
            simpa [hsub] using this
          exact this
    have hy_eq : y = 11 := by
      simpa [hx9, hcase] using rfl
    exact ⟨hx9, hy_eq⟩
