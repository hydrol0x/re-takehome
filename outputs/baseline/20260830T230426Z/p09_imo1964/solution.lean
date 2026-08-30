import Mathlib.Tactic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  constructor
  · intro hdiv
    -- turn the divisibility into a `ModEq`
    have hmod : (2 ^ n) ≡ 1 [MOD 7] := Nat.ModEq.of_dvd hdiv
    -- write `n = 3 * (n / 3) + n % 3`
    have hdecomp : n = 3 * (n / 3) + n % 3 := Nat.div_mod_eq_mul_add_mod n 3
    -- rewrite the exponent using this decomposition
    have hmod' : (2 ^ (3 * (n / 3)) * 2 ^ (n % 3)) ≡ 1 [MOD 7] := by
      simpa [hdecomp, Nat.pow_add] using hmod
    -- `2 ^ 3 ≡ 1 [MOD 7]`
    have h33 : (2 ^ 3 : ℕ) ≡ 1 [MOD 7] := by norm_num
    -- raise to the power `n / 3`
    have hpow3 : (2 ^ (3 * (n / 3))) ≡ 1 [MOD 7] := by
      have := h33.pow (n / 3)
      simpa [Nat.pow_mul] using this
    -- cancel the first factor
    have hfinal : (2 ^ (n % 3)) ≡ 1 [MOD 7] := by
      have hmul := hpow3.mul_right (2 ^ (n % 3))
      have : (2 ^ (3 * (n / 3)) * 2 ^ (n % 3)) ≡ (1 * 2 ^ (n % 3)) [MOD 7] := hmul
      have : (1 * 2 ^ (n % 3)) ≡ 1 [MOD 7] :=
        (Nat.ModEq.trans this.symm hmod')
      simpa using this
    -- analyse `n % 3`
    have hlt : n % 3 < 3 := Nat.mod_lt _ (by decide)
    have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
      interval_cases (n % 3) using hlt
    rcases hcases with rfl | rfl | rfl
    · -- case `n % 3 = 0`
      exact Nat.dvd_of_mod_eq_zero (by
        simpa [Nat.mod_mul_left_mod] using Nat.mod_eq_zero_of_dvd (Nat.dvd_refl 3))
    · -- case `n % 3 = 1` leads to contradiction
      have : (2 ^ 1 : ℕ) ≡ 1 [MOD 7] := by
        simpa using hfinal
      norm_num at this
    · -- case `n % 3 = 2` leads to contradiction
      have : (2 ^ 2 : ℕ) ≡ 1 [MOD 7] := by
        simpa using hfinal
      norm_num at this
  · intro h3
    rcases h3 with ⟨k, rfl⟩
    -- `2 ^ (3 * k) ≡ 1 [MOD 7]`
    have h33 : (2 ^ 3 : ℕ) ≡ 1 [MOD 7] := by norm_num
    have hpow : (2 ^ (3 * k)) ≡ 1 [MOD 7] := by
      have := h33.pow k
      simpa [Nat.pow_mul] using this
    exact (Nat.ModEq.dvd hpow)

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  intro hdiv
  -- turn the divisibility into a `ModEq`
  have hmod : (2 ^ n) ≡ 6 [MOD 7] := Nat.ModEq.of_dvd hdiv
  -- write `n = 3 * (n / 3) + n % 3`
  have hdecomp : n = 3 * (n / 3) + n % 3 := Nat.div_mod_eq_mul_add_mod n 3
  have hmod' : (2 ^ (3 * (n / 3)) * 2 ^ (n % 3)) ≡ 6 [MOD 7] := by
    simpa [hdecomp, Nat.pow_add] using hmod
  -- `2 ^ 3 ≡ 1 [MOD 7]`
  have h33 : (2 ^ 3 : ℕ) ≡ 1 [MOD 7] := by norm_num
  have hpow3 : (2 ^ (3 * (n / 3))) ≡ 1 [MOD 7] := by
    have := h33.pow (n / 3)
    simpa [Nat.pow_mul] using this
  -- cancel the first factor
  have hfinal : (2 ^ (n % 3)) ≡ 6 [MOD 7] := by
    have hmul := hpow3.mul_right (2 ^ (n % 3))
    have : (2 ^ (3 * (n / 3)) * 2 ^ (n % 3)) ≡ (1 * 2 ^ (n % 3)) [MOD 7] := hmul
    have : (1 * 2 ^ (n % 3)) ≡ 6 [MOD 7] :=
      (Nat.ModEq.trans this.symm hmod')
    simpa using this
  -- analyse `n % 3`
  have hlt : n % 3 < 3 := Nat.mod_lt _ (by decide)
  have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
    interval_cases (n % 3) using hlt
  rcases hcases with rfl | rfl | rfl
  · have : (2 ^ 0 : ℕ) ≡ 6 [MOD 7] := by simpa using hfinal
    norm_num at this
  · have : (2 ^ 1 : ℕ) ≡ 6 [MOD 7] := by simpa using hfinal
    norm_num at this
  · have : (2 ^ 2 : ℕ) ≡ 6 [MOD 7] := by simpa using hfinal
    norm_num at this
