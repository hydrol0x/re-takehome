import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

open Nat

/-- (a): `23 ∣ 2 ^ n - 1` iff `11 ∣ n`, for positive `n`. -/
theorem h02_a (n : ℕ) (hn : 0 < n) : 23 ∣ 2 ^ n - 1 ↔ 11 ∣ n := by
  -- rewrite the divisibility in terms of `ModEq`
  have hmod_eq : (2 ^ n) ≡ 1 [MOD 23] ↔ 23 ∣ 2 ^ n - 1 := (modEq_iff_dvd).symm
  have horder : (2 ^ 11) ≡ 1 [MOD 23] := by
    dsimp [ModEq]
    norm_num
  constructor
  · intro h
    have hmod : (2 ^ n) ≡ 1 [MOD 23] := (hmod_eq).mpr h
    -- write `n = 11 * q + r` with `r < 11`
    obtain ⟨q, r, hrlt, hqr⟩ := Nat.mod_mul_left_div_mod n 11
    have hpow : (2 ^ (11 * q)) ≡ 1 [MOD 23] := by
      have := horder.pow q
      simpa [pow_mul] using this
    have : (2 ^ n) ≡ (2 ^ r) [MOD 23] := by
      have : (2 ^ n) = (2 ^ (11 * q)) * 2 ^ r := by
        simpa [hqr, pow_add, pow_mul] using rfl
      simpa [this, hpow, one_mul] using (ModEq.rfl : (2 ^ n) ≡ (2 ^ n) [MOD 23])
    have hr : (2 ^ r) ≡ 1 [MOD 23] := (hmod.trans this.symm)
    -- check the only possible `r` is `0`
    have : r = 0 := by
      fin_cases r <;> norm_num at hr
    exact (Nat.dvd_of_mod_eq_zero (by
      simpa [Nat.mod_eq_of_lt hrlt, this] ))
  · intro h
    rcases h with ⟨k, hk⟩
    have : (2 ^ (11 * k)) ≡ 1 [MOD 23] := by
      have := horder.pow k
      simpa [pow_mul] using this
    have : (2 ^ n) ≡ 1 [MOD 23] := by
      simpa [hk, pow_mul] using this
    exact (hmod_eq).mp this

/-- (b): no positive `n` has `23 ∣ 2 ^ n + 1`. -/
theorem h02_b (n : ℕ) (hn : 0 < n) : ¬23 ∣ 2 ^ n + 1 := by
  intro h
  have hmod : (2 ^ n) ≡ (-1 : ℤ) [ZMOD 23] := by
    have : (2 ^ n + 1) ≡ 0 [ZMOD 23] := (ZMod.intCast_eq_intCast_iff).mpr h
    simpa [add_comm, sub_eq_add_neg] using this
  have horder : (2 ^ 11 : ℤ) ≡ 1 [ZMOD 23] := by
    norm_num
  have hpow : (2 ^ (11 * n)) ≡ 1 [ZMOD 23] := by
    have := horder.pow n
    simpa [pow_mul] using this
  have : (2 ^ (11 * n)) ≡ (-1 : ℤ) [ZMOD 23] := by
    simpa [pow_mul, mul_comm] using hmod
  have : (1 : ℤ) ≡ (-1 : ℤ) [ZMOD 23] := by
    simpa [hpow] using this
  have : (2 : ℤ) ≡ 0 [ZMOD 23] := by
    have : (2 : ℤ) ≡ 0 [ZMOD 23] := by
      have : (1 : ℤ) - (-1 : ℤ) ≡ 0 [ZMOD 23] := by
        simpa using this
      simpa [sub_eq, add_comm] using this
    exact this
  norm_num at this
