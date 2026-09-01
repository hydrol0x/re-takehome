import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Mathlib.GroupTheory.OrderOfElement

open Nat

/-- (a): `23 ∣ 2 ^ n - 1` iff `11 ∣ n`, for positive `n`. -/
theorem h02_a (n : ℕ) (hn : 0 < n) : 23 ∣ 2 ^ n - 1 ↔ 11 ∣ n := by
  -- work in the multiplicative group of units of `ZMod 23`
  have h2ne : (2 : ZMod 23) ≠ 0 := by norm_num
  let u : (ZMod 23)ˣ := Units.mk0 2 h2ne
  have hpow11 : (u : (ZMod 23)ˣ) ^ 11 = 1 := by
    change ((2 : ZMod 23) ^ 11) = 1
    norm_num
  have horder : orderOf u = 11 := by
    have hdiv : orderOf u ∣ 11 := (orderOf_dvd_iff_pow_eq_one).mpr hpow11
    have hprime : Nat.Prime 11 := by norm_num
    have hneq1 : orderOf u ≠ 1 := by
      intro h1
      have : (u : (ZMod 23)ˣ) = 1 := (orderOf_eq_one_iff).mp h1
      have : (2 : ZMod 23) = 1 := congrArg Units.val this
      norm_num at this
    rcases Nat.dvd_prime hprime hdiv with h | h
    · exact (hneq1 h).elim
    · exact h
  constructor
  · intro h
    -- turn the divisibility into an equality in `ZMod 23`
    have hmod : ((2 : ZMod 23) ^ n) = (1 : ZMod 23) := by
      have : (2 ^ n) ≡ 1 [MOD 23] := Nat.ModEq.of_dvd_sub h
      exact (ZMod.natCast_self_eq_zero_iff_dvd).mp
        (by
          change ((2 ^ n - 1) : ZMod 23) = 0
          simpa [sub_eq, Nat.cast_sub, Nat.cast_one] using
            (Nat.ModEq.sub_eq_zero_iff (a:=2 ^ n) (b:=1) (m:=23)).mpr this)
    -- use the description of the order of `u`
    have : (orderOf u) ∣ n := (orderOf_dvd_iff_pow_eq_one).mp hmod
    simpa [horder] using this
  · intro h
    rcases h with ⟨k, hk⟩
    -- rewrite the power using the divisor
    have : ((2 : ZMod 23) ^ (11 * k)) = (1 : ZMod 23) := by
      have : ((2 : ZMod 23) ^ 11) = (1 : ZMod 23) := by
        simpa using hpow11
      simpa [pow_mul, this] using rfl
    have : ((2 : ZMod 23) ^ n) = (1 : ZMod 23) := by
      simpa [hk, pow_mul] using this
    -- turn the equality back into a divisibility statement
    have : (2 ^ n - 1) % 23 = 0 := by
      change ((2 ^ n - 1) : ZMod 23) = 0
      simpa [sub_eq, Nat.cast_sub, Nat.cast_one] using congrArg (fun x : ZMod 23 => x) this
    exact (Nat.dvd_of_mod_eq_zero this)
