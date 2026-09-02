import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

open Nat

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  -- auxiliary equivalence between divisibility and ModEq
  have hiff :
      (7 ∣ 2 ^ n - 1) ↔ (2 ^ n) ≡ (1 : ℕ) [MOD 7] := by
    have h7 : (7 : ℕ) ≠ 0 := by decide
    simpa using (Nat.ModEq.dvd_iff_modEq (a := 2 ^ n) (b := 1) (n := 7) h7)
  -- the basic ModEq for the order of 2 modulo 7
  have h2pow3 : (2 ^ 3) ≡ (1 : ℕ) [MOD 7] := by norm_num
  constructor
  · intro hdiv
    have hmod : (2 ^ n) ≡ (1 : ℕ) [MOD 7] := (hiff.mp hdiv)
    -- write n = 3 * (n / 3) + n % 3
    have hn_eq : n = 3 * (n / 3) + n % 3 := by
      have := Nat.mod_add_div n 3
      -- this gives `n % 3 + 3 * (n / 3) = n`
      simpa [add_comm, mul_comm, add_left_comm, add_assoc] using this.symm
    -- reduce the exponent modulo 3 using the order
    have hpow3 : (2 ^ (3 * (n / 3))) ≡ (1 : ℕ) [MOD 7] := by
      have := (Nat.ModEq.pow h2pow3 (n / 3))
      simpa [pow_mul] using this
    have hpow_mod : (2 ^ n) ≡ (2 ^ (n % 3)) [MOD 7] := by
      have hmul := hpow3.mul (Nat.ModEq.refl (2 ^ (n % 3)))
      simpa [pow_add, hn_eq] using hmul
    have hfinal : (2 ^ (n % 3)) ≡ (1 : ℕ) [MOD 7] :=
      (hpow_mod.symm.trans hmod)
    have hmodpow : (2 ^ (n % 3)) % 7 = 1 := by
      simpa [Nat.ModEq] using hfinal
    -- analyse the possible values of n % 3
    have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
      have hlt : n % 3 < 3 := Nat.mod_lt _ (by decide)
      interval_cases (n % 3) using hlt
    rcases hcases with h0 | h1 | h2
    · -- the only possible case
      exact Nat.dvd_of_mod_eq_zero (by simpa [h0])
    · have : (2 ^ (1 : ℕ)) % 7 = 1 := by simpa [h1] using hmodpow
      norm_num at this
    · have : (2 ^ (2 : ℕ)) % 7 = 1 := by simpa [h2] using hmodpow
      norm_num at this
  · intro h3
    rcases Nat.exists_eq_mul_left_of_dvd h3 with ⟨k, rfl⟩
    have hpow : (2 ^ (3 * k)) ≡ (1 : ℕ) [MOD 7] := by
      have := (Nat.ModEq.pow h2pow3 k)
      simpa [pow_mul] using this
    have h7 : (7 : ℕ) ≠ 0 := by decide
    exact (Nat.ModEq.dvd_iff_modEq (a := 2 ^ (3 * k)) (b := 1) (n := 7) h7).mpr hpow

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  intro hdiv
  have h7 : (7 : ℕ) ≠ 0 := by decide
  have hmod : (2 ^ n) ≡ (-1 : ℤ) [ZMOD 7] := by
    -- turn the divisibility into a ModEq over ℤ
    have : (7 : ℤ) ∣ (2 ^ n : ℤ) + 1 := by
      simpa using hdiv
    have h := (Int.ModEq.dvd_iff_modEq (a := (2 ^ n : ℤ)) (b := (-1 : ℤ)) (n := (7 : ℤ)) (by decide)).mpr this
    simpa [Int.neg_one_mul, add_comm] using h
  -- reduce exponent modulo 3 as before, but now in ℤ
  have h2pow3 : (2 : ℤ) ^ 3 ≡ (1 : ℤ) [ZMOD 7] := by norm_num
  have hn_eq : (n : ℤ) = 3 * (n / 3) + n % 3 := by
    have := Nat.mod_add_div n 3
    have : (n % 3 : ℤ) + 3 * (n / 3) = n := by
      simpa using congrArg (fun x : ℕ => (x : ℤ)) this
    simpa [add_comm, mul_comm, add_left_comm, add_assoc] using this.symm
  have hpow3 : ((2 : ℤ) ^ (3 * (n / 3))) ≡ (1 : ℤ) [ZMOD 7] := by
    have := (Int.ModEq.pow h2pow3 (n / 3))
    simpa [pow_mul] using this
  have hpow_mod : ((2 : ℤ) ^ n) ≡ ((2 : ℤ) ^ (n % 3)) [ZMOD 7] := by
    have hmul := hpow3.mul (Int.ModEq.refl ((2 : ℤ) ^ (n % 3)))
    simpa [pow_add, hn_eq] using hmul
  have hfinal : ((2 : ℤ) ^ (n % 3)) ≡ (-1 : ℤ) [ZMOD 7] :=
    (hpow_mod.symm.trans hmod)
  have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
    have hlt : n % 3 < 3 := Nat.mod_lt _ (by decide)
    interval_cases (n % 3) using hlt
  rcases hcases with h0 | h1 | h2
  · have : ((2 : ℤ) ^ (0 : ℕ)) ≡ (-1 : ℤ) [ZMOD 7] := by simpa [h0] using hfinal
    norm_num at this
  · have : ((2 : ℤ) ^ (1 : ℕ)) ≡ (-1 : ℤ) [ZMOD 7] := by simpa [h1] using hfinal
    norm_num at this
  · have : ((2 : ℤ) ^ (2 : ℕ)) ≡ (-1 : ℤ) [ZMOD 7] := by simpa [h2] using hfinal
    norm_num at this
