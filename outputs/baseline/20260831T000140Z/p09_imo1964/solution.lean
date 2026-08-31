import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

open Nat

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  -- rewrite the divisibility condition as a `ModEq`
  have h7 : (2 ^ n) ≡ 1 [MOD 7] ↔ 7 ∣ 2 ^ n - 1 := by
    constructor
    · intro h
      rcases (Nat.ModEq.dvd_iff h) with ⟨k, hk⟩
      exact ⟨k, by
        have : 2 ^ n - 1 = 7 * k := by
          simpa [Nat.sub_eq_iff_eq_add] using hk
        simpa [this]⟩
    · intro h
      rcases h with ⟨k, hk⟩
      have : 2 ^ n = 7 * k + 1 := by
        simpa [Nat.sub_eq_iff_eq_add] using hk
      have : (2 ^ n) % 7 = 1 := by
        simpa [this] using Nat.mod_add_left_mod (7 * k) 1 7
      exact (Nat.ModEq.ofNat _ _).mpr this
  -- the order of 2 modulo 7 is 3
  have h23 : (2 : ℕ) ^ 3 ≡ 1 [MOD 7] := by norm_num
  -- reduce the exponent modulo 3
  have hred (m : ℕ) : (2 : ℕ) ^ m ≡ (2 ^ (m % 3)) [MOD 7] := by
    have hdecomp : m = 3 * (m / 3) + m % 3 := by
      simpa [Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div m 3).symm
    have hpow :
        (2 : ℕ) ^ (3 * (m / 3)) ≡ 1 [MOD 7] := by
      have := (Nat.ModEq.pow h23 (m / 3))
      simpa [Nat.pow_mul] using this
    have := (Nat.ModEq.mul_left (2 ^ (m % 3)) hpow)
    simpa [Nat.pow_add, Nat.pow_mul, hdecomp, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using this
  -- now finish the equivalence
  constructor
  · intro h
    have : (2 ^ n) ≡ 1 [MOD 7] := (h7.mp h)
    have : (2 ^ (n % 3)) ≡ 1 [MOD 7] := (hred n).trans this
    have hcases : n % 3 = 0 := by
      have hlt : n % 3 < 3 := Nat.mod_lt _ (by decide)
      rcases Nat.mod_eq_of_lt hlt with rfl | rfl | rfl <;> 
        (simp [Nat.mod_eq_of_lt (by decide)] at this; 
         try contradiction)
    exact ⟨n / 3, by
      have := Nat.mod_mul_left_mod n 3
      simpa [hcases, Nat.mul_comm] using this⟩
  · rintro ⟨k, hk⟩
    have : n = 3 * k := hk
    have : (2 : ℕ) ^ n ≡ 1 [MOD 7] := by
      simpa [this, Nat.pow_mul] using (Nat.ModEq.pow h23 k)
    exact h7.mpr this

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  intro h
  have hmod : (2 ^ n) ≡ (-1) [MOD 7] := by
    rcases (Nat.ModEq.dvd_iff (a:=2^n) (b:=(-1 : ℕ)) (n:=7)) with ⟨k, hk⟩
    have : 2 ^ n + 1 = 7 * k := h
    have : 2 ^ n = 7 * k - 1 := by
      simpa [Nat.add_comm, Nat.sub_eq_iff_eq_add] using this
    have : (2 ^ n) % 7 = 6 := by
      simpa [this] using Nat.mod_sub_left_mod (7 * k) 1 7
    exact (Nat.ModEq.ofNat _ _).mpr this
  have h23 : (2 : ℕ) ^ 3 ≡ 1 [MOD 7] := by norm_num
  have hred : (2 : ℕ) ^ n ≡ (2 ^ (n % 3)) [MOD 7] := by
    have hdecomp : n = 3 * (n / 3) + n % 3 := by
      simpa [Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div n 3).symm
    have hpow :
        (2 : ℕ) ^ (3 * (n / 3)) ≡ 1 [MOD 7] := by
      have := (Nat.ModEq.pow h23 (n / 3))
      simpa [Nat.pow_mul] using this
    have := (Nat.ModEq.mul_left (2 ^ (n % 3)) hpow)
    simpa [Nat.pow_add, Nat.pow_mul, hdecomp, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using this
  have : (2 ^ (n % 3)) ≡ (-1) [MOD 7] := (hred.trans hmod)
  have hlt : n % 3 < 3 := Nat.mod_lt _ (by decide)
  rcases Nat.mod_eq_of_lt hlt with rfl | rfl | rfl <;>
    (norm_num at this)
