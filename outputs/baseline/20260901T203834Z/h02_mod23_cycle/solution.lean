import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

open Nat

/-- Helper: the multiplicative order of `2` in `ZMod 23` is `11`. -/
lemma orderOf_two_mod23 : (orderOf (2 : ZMod 23)) = 11 := by
  have hpow : (2 : ZMod 23) ^ 11 = 1 := by norm_num
  have hdiv : (orderOf (2 : ZMod 23)) ∣ 11 :=
    (orderOf_dvd_iff_pow_eq_one).mpr hpow
  have hpos : (orderOf (2 : ZMod 23)) ≠ 0 := by
    have hne : (2 : ZMod 23) ≠ 0 := by norm_num
    exact (orderOf_ne_zero_iff).mpr hne
  rcases Nat.dvd_prime (by decide : Nat.Prime 11) hdiv with h | h
  · exact (hpos (by simpa [h] ))
  · exact h

/-- (a): `23 ∣ 2 ^ n - 1` iff `11 ∣ n`, for positive `n`. -/
theorem h02_a (n : ℕ) (hn : 0 < n) : 23 ∣ 2 ^ n - 1 ↔ 11 ∣ n := by
  -- rewrite the divisibility condition in `ZMod 23`
  have h₁ : (23 ∣ 2 ^ n - 1) ↔ ((2 : ZMod 23) ^ n = (1 : ZMod 23)) := by
    have hpos : 1 ≤ 2 ^ n := by
      have : 0 < n := hn
      have : 2 ^ n ≥ 2 := by
        have : 1 ≤ n := Nat.succ_le_of_lt hn
        exact Nat.pow_le_pow_of_le_left (by decide : 1 ≤ 2) this
      exact le_trans (Nat.succ_le_of_lt (Nat.zero_lt_one)) this
    constructor
    · intro h
      have : ((2 ^ n - 1) : ZMod 23) = 0 := by
        exact (ZMod.natCast_self).mpr h
      have : (2 : ZMod 23) ^ n - 1 = 0 := by
        simpa [Nat.cast_pow, Nat.cast_one, Nat.cast_sub hpos] using this
      simpa [sub_eq, sub_eq_add_neg] using sub_eq_zero.mp this
    · intro h
      have : (2 : ZMod 23) ^ n - 1 = (0 : ZMod 23) := by
        simpa [h] using sub_self (1 : ZMod 23)
      have : ((2 ^ n - 1) : ZMod 23) = 0 := by
        simpa [Nat.cast_pow, Nat.cast_one, Nat.cast_sub hpos] using this
      exact (ZMod.natCast_self).mp this
  -- use the order of `2` modulo `23`
  have h₂ : ((2 : ZMod 23) ^ n = (1 : ZMod 23)) ↔ 11 ∣ n := by
    have horder := orderOf_two_mod23
    have hpow : (2 : ZMod 23) ^ 11 = (1 : ZMod 23) := by
      simpa [horder] using (orderOf_pow_eq_one (2 : ZMod 23)).mpr rfl
    constructor
    · intro h
      have : (orderOf (2 : ZMod 23)) ∣ n :=
        (orderOf_dvd_iff_pow_eq_one).mp (by simpa [horder] using h)
      simpa [horder] using this
    · intro h
      rcases Nat.dvd_of_modEq_zero (by decide : (11 : ℕ) ≠ 0) h with ⟨k, rfl⟩
      simpa [pow_mul, hpow] using rfl
  exact h₁.trans h₂

/-- (b): no positive `n` has `23 ∣ 2 ^ n + 1`. -/
theorem h02_b (n : ℕ) (hn : 0 < n) : ¬23 ∣ 2 ^ n + 1 := by
  intro h
  have hmod : ((2 : ZMod 23) ^ n : ZMod 23) = -1 := by
    have hpos : 1 ≤ 2 ^ n := by
      have : 0 < n := hn
      have : 2 ^ n ≥ 2 := by
        have : 1 ≤ n := Nat.succ_le_of_lt hn
        exact Nat.pow_le_pow_of_le_left (by decide : 1 ≤ 2) this
      exact le_trans (Nat.succ_le_of_lt (Nat.zero_lt_one)) this
    have : ((2 ^ n + 1) : ZMod 23) = 0 := (ZMod.natCast_self).mpr h
    have : (2 : ZMod 23) ^ n + 1 = (0 : ZMod 23) := by
      simpa [Nat.cast_pow, Nat.cast_one, Nat.cast_add, Nat.cast_one] using this
    have : (2 : ZMod 23) ^ n = -1 := by
      simpa using eq_neg_of_add_eq_zero_left this
    exact this
  have horder := orderOf_two_mod23
  have hpow : (2 : ZMod 23) ^ 11 = (1 : ZMod 23) := by
    simpa [horder] using (orderOf_pow_eq_one (2 : ZMod 23)).mpr rfl
  have hodd : (2 : ZMod 23) ^ (2 * 11) = (1 : ZMod 23) := by
    simpa [pow_mul, hpow] using rfl
  have hneg : (2 : ZMod 23) ^ (2 * 11) = ((-1 : ZMod 23) ^ 2) := by
    simpa [hmod] using congrArg (fun x : ZMod 23 => x ^ (2 * 11)) hmod
  have : ((-1 : ZMod 23) ^ 2) = (1 : ZMod 23) := by norm_num
  have : (2 : ZMod 23) ^ (2 * 11) = (1 : ZMod 23) := by
    simpa [this] using hneg
  have hdiv : (orderOf (2 : ZMod 23)) ∣ 2 * 11 :=
    (orderOf_dvd_iff_pow_eq_one).mpr this
  have : (orderOf (2 : ZMod 23)) = 11 := by
    simpa [horder] using hdiv
  have : (2 : ZMod 23) ^ (2 * 11) = (1 : ZMod 23) := by
    simpa [pow_mul, hpow] using rfl
  have : ((-1 : ZMod 23) ^ (2 * 11)) = (1 : ZMod 23) := by
    simpa [hmod] using congrArg (fun x : ZMod 23 => x ^ (2 * 11)) hmod
  have : ((-1 : ZMod 23) ^ 22) = (1 : ZMod 23) := by simpa using this
  have : ((-1 : ZMod 23) ^ 22) = (1 : ZMod 23) := by norm_num
  have : ((-1 : ZMod 23) ^ 22) = (1 : ZMod 23) := this
  have hodd' : ((-1 : ZMod 23) ^ 11) = (-1 : ZMod 23) := by
    have : ((-1 : ZMod 23) ^ 11) * ((-1 : ZMod 23) ^ 11) = (1 : ZMod 23) := by
      simpa [pow_mul] using this
    have hne : ((-1 : ZMod 23) ^ 11) ≠ 0 := by norm_num
    have := mul_left_cancel₀ hne this
    simpa using this
  have : ((2 : ZMod 23) ^ 11) = (1 : ZMod 23) := by
    simpa [horder] using (orderOf_pow_eq_one (2 : ZMod 23)).mpr rfl
  have : ((2 : ZMod 23) ^ 11) = (-1 : ZMod 23) := by
    simpa [hmod] using congrArg (fun x : ZMod 23 => x ^ 11) hmod
  have : (1 : ZMod 23) = (-1 : ZMod 23) := by
    simpa [hpow] using this
  have : (2 : ZMod 23) = (0 : ZMod 23) := by
    have : (2 : ZMod 23) = (1 : ZMod 23) + (1 : ZMod 23) := by norm_num
    simpa [this] using congrArg (fun x : ZMod 23 => x + 1) this
  have : (2 : ZMod 23) = (0 : ZMod 23) := by norm_num
  have : False := by
    have hneq : (2 : ZMod 23) ≠ 0 := by norm_num
    exact hneq this
  exact this.elim
