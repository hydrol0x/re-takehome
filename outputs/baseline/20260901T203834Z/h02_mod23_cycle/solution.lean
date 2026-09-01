import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

open Nat

/-- (a): `23 ∣ 2 ^ n - 1` iff `11 ∣ n`, for positive `n`. -/
theorem h02_a (n : ℕ) (hn : 0 < n) : 23 ∣ 2 ^ n - 1 ↔ 11 ∣ n := by
  -- work in the multiplicative group of units of `ZMod 23`
  have h23 : (23 : ℕ) ≠ 0 := by decide
  let g : (ZMod 23)ˣ := (2 : ZMod 23)⁻¹
  have hg : (2 : ZMod 23) ∈ (Units (ZMod 23)) := by
    have : (2 : ZMod 23) ≠ 0 := by
      decide
    exact Units.mk0 _ this
  have horder : orderOf (2 : (ZMod 23)ˣ) = 11 := by
    -- `norm_num` can compute the order of a unit in a small field
    norm_num
  -- rewrite the statement in terms of `ZMod`
  have hdiv_iff : (23 ∣ 2 ^ n - 1) ↔ ((2 ^ n : ℕ) : ZMod 23) = 1 := by
    constructor
    · intro h
      have : ((2 ^ n - 1) : ZMod 23) = 0 := by
        exact (ZMod.natCast_self (n := 23) (a := 2 ^ n - 1)).symm ▸
          (ZMod.natCast_self (n := 23)).trans (by
            exact (ZMod.natCast_self (n := 23)).symm)
      simpa [sub_eq, sub_eq_add_neg, map_sub, map_one, map_pow] using this
    · intro h
      have : ((2 ^ n - 1) : ZMod 23) = 0 := by
        simpa [sub_eq, sub_eq_add_neg, map_sub, map_one, map_pow, h]
      exact (ZMod.natCast_self (n := 23) (a := 2 ^ n - 1)).mp this
  -- use the order of `2` in the group of units
  have hpow : ((2 : ZMod 23) ^ n = (1 : ZMod 23)) ↔ 11 ∣ n := by
    have : ((2 : ZMod 23) ^ n = (1 : ZMod 23)) ↔ (orderOf (2 : (ZMod 23)ˣ)) ∣ n := by
      simpa [pow_eq, horder] using
        (orderOf_pow_eq_one_iff (a := (2 : (ZMod 23)ˣ)) (n := n)).symm
    simpa [horder] using this
  simpa [hdiv_iff, map_pow] using hpow

/-- (b): no positive `n` has `23 ∣ 2 ^ n + 1`. -/
theorem h02_b (n : ℕ) (hn : 0 < n) : ¬23 ∣ 2 ^ n + 1 := by
  intro h
  have hmod : ((2 : ZMod 23) ^ n = (-1 : ZMod 23)) := by
    have : ((2 ^ n + 1 : ℕ) : ZMod 23) = 0 := by
      have : ((2 ^ n + 1) : ZMod 23) = ((2 ^ n : ℕ) : ZMod 23) + 1 := by rfl
      simpa [this] using
        (ZMod.natCast_self (n := 23) (a := 2 ^ n + 1)).mp h
    have : ((2 : ZMod 23) ^ n) = -1 := by
      have : ((2 : ZMod 23) ^ n) + (1 : ZMod 23) = 0 := by
        simpa [map_pow, map_one] using this
      exact eq_neg_of_add_eq_zero_left this
    exact this
  have horder : orderOf (2 : (ZMod 23)ˣ) = 11 := by
    norm_num
  have hpow : ((2 : ZMod 23) ^ (2 * 11) = 1) := by
    have : ((2 : (ZMod 23)ˣ) ^ (2 * 11) : (ZMod 23)ˣ) = 1 := by
      simpa [pow_mul, horder] using (orderOf_pow_eq_one (a := (2 : (ZMod 23)ˣ)) (k := 2))
    exact congrArg Units.val this
  have : ((2 : ZMod 23) ^ (2 * 11) = (-1 : ZMod 23) ^ (2 * 11)) := by
    simpa [hmod] using congrArg (fun x : ZMod 23 => x ^ (2 * 11)) hmod
  have : ((-1 : ZMod 23) ^ (2 * 11) = (1 : ZMod 23)) := by
    simpa using (one_pow (2 * 11))
  have : ((2 : ZMod 23) ^ (2 * 11) = (1 : ZMod 23)) := by
    simpa [this] using this
  have hcontr : (1 : ZMod 23) = (-1 : ZMod 23) := by
    calc
      (1 : ZMod 23) = ((2 : ZMod 23) ^ (2 * 11)) := (hpow.symm)
      _ = ((2 : ZMod 23) ^ n) ^ (2 * 11 / n) := by
        sorry
      _ = (-1 : ZMod 23) ^ (2 * 11 / n) := by
        sorry
      _ = (-1 : ZMod 23) := by
        have : (2 * 11 / n) % 2 = 1 := by sorry
        simpa [pow_mul] using this
  have : (2 : ZMod 23) = 0 := by
    have : (1 : ZMod 23) - (-1 : ZMod 23) = 0 := by simpa [hcontr] using sub_self (1 : ZMod 23)
    simpa using this
  have : (2 : ℕ) % 23 ≠ 0 := by decide
  exact this (by simpa using congrArg ZMod.val this)
