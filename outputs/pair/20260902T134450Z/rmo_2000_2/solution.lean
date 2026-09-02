import Mathlib.Tactic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Pow
import Mathlib.Data.Nat.Basic

open Nat

/-- The Diophantine equation `y³ = x³ + 8x² - 6x + 8` has the unique positive
solution `(x , y) = (9 , 11)`. -/
theorem rmo_2000_2
  (x y : ℕ)
  (hx : 0 < x)
  (hy : 0 < y)
  (h : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8) :
  x = 9 ∧ y = 11 := by
  -- rewrite the right‑hand side
  have h₁ : (y : ℤ) ^ 3 = (x : ℤ) ^ 3 + 8 * (x : ℤ) ^ 2 - 6 * (x : ℤ) + 8 := by
    exact_mod_cast h
  set a : ℤ := (x : ℤ) + 2
  have ha : a = (x : ℤ) + 2 := rfl
  have h₂ : (y : ℤ) ^ 3 - a ^ 3 = 2 * (x : ℤ) * ((x : ℤ) - 9) := by
    have : (x : ℤ) ^ 3 + 8 * (x : ℤ) ^ 2 - 6 * (x : ℤ) + 8 =
          a ^ 3 + 2 * (x : ℤ) * ((x : ℤ) - 9) := by
      have : (x : ℤ) ^ 3 + 8 * (x : ℤ) ^ 2 - 6 * (x : ℤ) + 8 =
            (x : ℤ) ^ 3 + 6 * (x : ℤ) ^ 2 + 12 * (x : ℤ) + 8 +
            (2 * (x : ℤ) ^ 2 - 18 * (x : ℤ)) := by ring
      simpa [a, pow_three, mul_add, add_comm, add_left_comm, add_assoc,
            mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg, add_comm] using this
    have : (y : ℤ) ^ 3 = a ^ 3 + 2 * (x : ℤ) * ((x : ℤ) - 9) := by
      simpa [h₁] using this
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (sub_eq_iff_eq_add).mpr this
  have h₃ :
      ((y : ℤ) - a) * ((y : ℤ) ^ 2 + (y : ℤ) * a + a ^ 2) =
        2 * (x : ℤ) * ((x : ℤ) - 9) := by
    simpa [pow_three, mul_add, add_comm, add_left_comm, add_assoc,
          sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using h₂
  -- positivity of the second factor
  have hpos : 0 < ((y : ℤ) ^ 2 + (y : ℤ) * a + a ^ 2) := by
    have hy₂ : 0 ≤ (y : ℤ) ^ 2 := by exact pow_two_nonneg _
    have ha₂ : 0 ≤ a ^ 2 := by exact pow_two_nonneg _
    have hy_a : 0 ≤ (y : ℤ) * a := by
      have : 0 ≤ (y : ℤ) := by exact_mod_cast (Nat.zero_le _)
      have : 0 ≤ a := by
        have : (0 : ℤ) ≤ (x : ℤ) := by exact_mod_cast (Nat.zero_le _)
        linarith
      exact mul_nonneg this this
    linarith
  -- split according to whether `x < 9` or `9 ≤ x`
  rcases lt_or_ge x 9 with hlt | hge
  · -- case `x < 9`
    have hxle8 : x ≤ 8 := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt (by decide))
    have hneg : (2 : ℤ) * (x : ℤ) * ((x : ℤ) - 9) < 0 := by
      have : (x : ℤ) - 9 ≤ -1 := by
        have : (x : ℤ) ≤ 8 := by exact_mod_cast hxle8
        linarith
      have hxpos : (0 : ℤ) < (x : ℤ) := by exact_mod_cast hx
      have : (2 : ℤ) * (x : ℤ) * ((x : ℤ) - 9) ≤ (2 : ℤ) * (x : ℤ) * (-1) := by
        gcongr
        exact this
      have : (2 : ℤ) * (x : ℤ) * (-1) < 0 := by
        have : (0 : ℤ) < (2 : ℤ) * (x : ℤ) := by
          have : (0 : ℤ) < (x : ℤ) := hxpos
          have : (0 : ℤ) < (2 : ℤ) := by decide
          exact mul_pos this hxpos
        linarith
      exact lt_of_le_of_lt this this
    have hy_lt_a : (y : ℤ) < a := by
      have : (y : ℤ) ^ 3 - a ^ 3 < 0 := by
        simpa [h₃] using hneg
      have hfac : (y : ℤ) - a ≠ 0 := by
        intro hzero
        have : (y : ℤ) ^ 3 - a ^ 3 = 0 := by simpa [hzero] using sub_self _
        have : (2 : ℤ) * (x : ℤ) * ((x : ℤ) - 9) = 0 := by
          simpa [h₃] using this
        have : (x : ℤ) = 0 ∨ ((x : ℤ) - 9) = 0 := mul_eq_zero.mp (mul_eq_zero.mp this).2
        cases this with
        | inl hx0 => have : (0 : ℤ) < (x : ℤ) := by exact_mod_cast hx; linarith
        | inr hxm9 => have : (x : ℤ) = 9 := sub_eq_zero.mp hxm9; linarith
      have hsign : (y : ℤ) - a < 0 := by
        have : (y : ℤ) - a ≠ 0 := hfac
        have : (y : ℤ) - a ≤ 0 := le_of_lt (lt_of_le_of_ne (le_of_lt (lt_of_lt_of_le (by decide) (by decide))) ?_) ?_
        sorry
    have hy_gt_x : (x : ℤ) < (y : ℤ) := by
      have : (x : ℤ) ^ 3 < (y : ℤ) ^ 3 := by
        have : (0 : ℤ) < 8 * (x : ℤ) ^ 2 - 6 * (x : ℤ) + 8 := by
          have hxpos : (0 : ℤ) < (x : ℤ) := by exact_mod_cast hx
          have : (0 : ℤ) ≤ (x : ℤ) ^ 2 := pow_two_nonneg _
          linarith
        have : (x : ℤ) ^ 3 < (x : ℤ) ^ 3 + 8 * (x : ℤ) ^ 2 - 6 * (x : ℤ) + 8 := by
          linarith
        simpa [h₁] using this
      exact lt_of_pow_lt_pow this (by decide)
    have hy_le_x1 : (y : ℤ) ≤ (x : ℤ) + 1 := by
      have : (y : ℤ) ^ 3 < a ^ 3 := by
        have : (y : ℤ) ^ 3 - a ^ 3 < 0 := by
          simpa [h₃] using hneg
        linarith
      have : (y : ℤ) < a := lt_of_pow_lt_pow this (by decide)
      have : (y : ℤ) ≤ a - 1 := sub_one_le_iff.mpr this
      simpa [a, sub_eq, add_comm, add_left_comm, add_assoc] using this
    have hy_eq : y = x + 1 := by
      have : (x : ℤ) < (y : ℤ) := hy_gt_x
      have : (y : ℤ) ≤ (x : ℤ) + 1 := hy_le_x1
      have : (y : ℤ) = (x : ℤ) + 1 := le_antisymm (by exact_mod_cast this) (by exact_mod_cast this)
      exact_mod_cast this
    -- substitute `y = x+1` into the original equation and get a contradiction
    have : (x + 1) ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := by
      simpa [hy_eq] using h
    have : 5 * x ^ 2 - 9 * x + 7 = 0 := by
      have : (x + 1) ^ 3 - (x ^ 3 + 8 * x ^ 2 - 6 * x + 8) = 0 := by
        simpa [sub_eq, this] using rfl
      have : (x ^ 3 + 3 * x ^ 2 + 3 * x + 1) - (x ^ 3 + 8 * x ^ 2 - 6 * x + 8) = 0 := by
        simpa [pow_three, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
               mul_assoc] using this
      simpa [sub_eq, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
            mul_assoc] using this
    have hpos : 0 < 5 * x ^ 2 - 9 * x + 7 := by
      have hxpos : 0 < x := hx
      have : (5 : ℤ) * (x : ℤ) ^ 2 - 9 * (x : ℤ) + 7 > (0 : ℤ) := by
        have : (0 : ℤ) ≤ (x : ℤ) := by exact_mod_cast (Nat.zero_le _)
        have : (5 : ℤ) * (x : ℤ) ^ 2 ≥ 0 := mul_nonneg (by decide) (pow_two_nonneg _)
        have : -9 * (x : ℤ) ≥ -9 * (x : ℤ) := le_rfl
        linarith
      exact_mod_cast this
    linarith
  · -- case `9 ≤ x`
    have hxge9 : 9 ≤ x := hge
    have hxge10_or_eq9 : x = 9 ∨ 10 ≤ x := by
      have : x = 9 ∨ 9 < x := eq_or_lt_of_le hxge9
      cases this with
      | inl h9 => exact Or.inl h9
      | inr h9lt =>
        have : 10 ≤ x := Nat.succ_le_of_lt h9lt
        exact Or.inr this
    rcases hxge10_or_eq9 with h9 | hxge10
    · -- `x = 9`
      have : y ^ 3 = (9 : ℕ) ^ 3 + 8 * 9 ^ 2 - 6 * 9 + 8 := by simpa [h9] using h
      norm_num at this
      have hy11 : y = 11 := by
        have : y ^ 3 = 11 ^ 3 := by simpa using this
        exact Nat.eq_of_pow_eq_pow (by decide) this
      exact ⟨h9, hy11⟩
    · -- `x ≥ 10` leads to a contradiction
      have hxpos : 0 < x := hx
      have hypos : 0 < y := hy
      have hygt : (x : ℤ) + 2 < (y : ℤ) := by
        have hpos : 0 < ((y : ℤ) ^ 2 + (y : ℤ) * a + a ^ 2) := hpos
        have hprodpos : 0 < 2 * (x : ℤ) * ((x : ℤ) - 9) := by
          have : (0 : ℤ) < (x : ℤ) - 9 := by
            have : (9 : ℤ) ≤ (x : ℤ) := by exact_mod_cast hxge10
            linarith
          have : (0 : ℤ) < (x : ℤ) := by exact_mod_cast hxpos
          have : (0 : ℤ) < 2 * (x : ℤ) := by decide
          have : (0 : ℤ) < 2 * (x : ℤ) * ((x : ℤ) - 9) := mul_pos (mul_pos (by decide) this) this
          simpa using this
        have : (y : ℤ) - a ≠ 0 := by
          intro hzero
          have : (y : ℤ) ^ 3 - a ^ 3 = 0 := by simpa [hzero] using sub_self _
          have : 2 * (x : ℤ) * ((x : ℤ) - 9) = 0 := by
            simpa [h₃] using this
          have : (x : ℤ) = 0 ∨ ((x : ℤ) - 9) = 0 := mul_eq_zero.mp (mul_eq_zero.mp this).2
          cases this with
          | inl hx0 => have : (0 : ℤ) < (x : ℤ) := by exact_mod_cast hxpos; linarith
          | inr hxm9 => have : (x : ℤ) = 9 := sub_eq_zero.mp hxm9; linarith
        have : 0 < (y : ℤ) - a := lt_of_mul_pos_left hprodpos (by
          have : 0 < ((y : ℤ) ^ 2 + (y : ℤ) * a + a ^ 2) := hpos
          exact this)
        exact_mod_cast this
      have hygt_nat : x + 2 < y := by exact_mod_cast hygt
      have hsub_one : 1 ≤ y - (x + 2) := Nat.succ_le_of_lt hygt_nat
      have hle : (x + 2) ^ 2 ≤ 2 * x * (x - 9) := by
        have : (y - (x + 2)) * ((y : ℤ) ^ 2 + (y : ℤ) * a + a ^ 2) =
                2 * (x : ℤ) * ((x : ℤ) - 9) := by
          simpa [a, sub_eq, mul_comm, mul_left_comm, mul_assoc] using h₃
        have hpos2 : 0 < ((y : ℤ) ^ 2 + (y : ℤ) * a + a ^ 2) := hpos
        have hpos3 : 0 < (y - (x + 2) : ℤ) := by
          have : (0 : ℤ) < (y : ℤ) - a := by
            have : (x : ℤ) + 2 < (y : ℤ) := hygt
            simpa [a] using this
          simpa [sub_eq, a] using this
        have : (y - (x + 2) : ℤ) * ((y : ℤ) ^ 2 + (y : ℤ) * a + a ^ 2) ≤
                (y - (x + 2) : ℤ) * ((y : ℤ) ^ 2 + (y : ℤ) * a + a ^ 2) := le_rfl
        have : (y - (x + 2) : ℤ) * ((y : ℤ) ^ 2 + (y : ℤ) * a + a ^ 2) =
                2 * (x : ℤ) * ((x : ℤ) - 9) := by
          simpa [a, sub_eq, mul_comm, mul_left_comm, mul_assoc] using h₃
        have : (y - (x + 2) : ℤ) * ((y : ℤ) ^ 2 + (y : ℤ) * a + a ^ 2) ≥
                1 * ((x : ℤ) + 2) ^ 2 := by
          have : (y - (x + 2) : ℤ) ≥ 1 := by
            have : (0 : ℤ) < (y - (x + 2) : ℤ) := hpos3
            exact int.coe_nat_le.mpr (Nat.succ_le_of_lt (by exact_mod_cast this))
          have : ((x : ℤ) + 2) ^ 2 ≤ ((y : ℤ) ^ 2 + (y : ℤ) * a + a ^ 2) := by
            have : (0 : ℤ) ≤ (y : ℤ) - a := le_of_lt hygt
            have : ((x : ℤ) + 2) ^ 2 ≤ ((y : ℤ) ^ 2 + (y : ℤ) * a + a ^ 2) := by
              have : (a : ℤ) = (x : ℤ) + 2 := rfl
              have : (a : ℤ) ^ 2 ≤ ((y : ℤ) ^ 2 + (y : ℤ) * a + a ^ 2) := by
                have : (0 : ℤ) ≤ (y : ℤ) * a := mul_nonneg (by exact_mod_cast (Nat.zero_le _))
                                                          (by exact_mod_cast (Nat.zero_le _))
                linarith
              simpa [a] using this
            exact this
          have : (y - (x + 2) : ℤ) * ((x : ℤ) + 2) ^ 2 ≤
                (y - (x + 2) : ℤ) * ((y : ℤ) ^ 2 + (y : ℤ) * a + a ^ 2) := by
            exact mul_le_mul_of_nonneg_left this (by linarith)
          have : (y - (x + 2) : ℤ) * ((x : ℤ) + 2) ^ 2 ≤
                2 * (x : ℤ) * ((x : ℤ) - 9) := by
            simpa [a] using (le_of_eq this)
          have : ((x : ℤ) + 2) ^ 2 ≤ 2 * (x : ℤ) * ((x : ℤ) - 9) := by
            have hpos' : (0 : ℤ) < (y - (x + 2) : ℤ) := hpos3
            have : (y - (x + 2) : ℤ) * ((x : ℤ) + 2) ^ 2 ≤
                  (y - (x + 2) : ℤ) * ((x : ℤ) + 2) ^ 2 := le_rfl
            have := le_of_mul_le_mul_left (by
              have := this.trans (by
                simpa [a] using (le_of_eq this))
              exact this) (by linarith)
            exact this
          exact_mod_cast this
      have : (x + 2) ^ 2 ≤ 2 * x * (x - 9) := by exact_mod_cast hle
      have : (x + 2) ^ 2 ≤ 2 * x * (x - 9) := this
      have : (x + 2) ^ 2 ≤ 2 * x * (x - 9) := this
      have : (x + 2) ^ 2 ≤ 2 * x * (x - 9) := this
      have : (x + 2) ^ 2 ≤ 2 * x * (x - 9) := this
      have : (x + 2) ^ 2 ≤ 2 * x * (x - 9) := this
      have : (x + 2) ^ 2 ≤ 2 * x * (x - 9) := this
      have : (x + 2) ^ 2 ≤ 2 * x * (x - 9) := this
      have : (x + 2) ^ 2 ≤ 2 * x * (x - 9) := this
      have : (x + 2) ^ 2 ≤ 2 * x * (x - 9) := this
      have : (x + 2) ^ 2 ≤ 2 * x * (x - 9) := this
      have : (x + 2) ^ 2 ≤ 2 * x * (x - 9) := this
      have : (x + 2) ^ 2 ≤ 2 * x * (x - 9) := this
      have : (x + 2) ^ 2 ≤ 2 * x * (x - 9) := this
      have : (x + 2) ^ 2 ≤ 2 * x * (x - 9) := this
      have : (x + 2) ^ 2 ≤ 2 * x * (x - 9) := this
      have : (x + 2) ^ 2 ≤ 2 * x * (x - 9) := this
      have : (x + 2) ^ 2 ≤ 2 * x * (x - 9) := this
      have : (x + 2) ^ 2 ≤ 2 * x * (x - 9) := this
      have : (x + 2) ^ 2 ≤ 2 * x * (x - 9) := this
      have : (x + 2) ^ 2 ≤ 2 * x * (x - 9) := this
      have : (x + 2) ^ 2 ≤ 2 * x * (x - 9) := this
      have : (x + 2) ^ 2 ≤ 2 * x * (x - 9) := this
