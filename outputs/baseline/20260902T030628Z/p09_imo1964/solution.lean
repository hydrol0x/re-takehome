import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Linarith

open Nat

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  have h23 : (2 : ℕ) ^ 3 ≡ (1 : ℕ) [MOD 7] := by
    norm_num
  constructor
  · intro h7
    -- turn the divisibility into a `ModEq`
    have hmod : (2 ^ n) ≡ (1 : ℕ) [MOD 7] :=
      (Nat.modEq_iff_dvd).mpr h7
    -- write `n = 3 * q + r` with `r < 3`
    set q := n / 3 with hq
    set r := n % 3 with hr
    have hn_eq : n = 3 * q + r := by
      have := Nat.mod_add_div n 3
      -- `n % 3 + 3 * (n / 3) = n`
      simpa [hq, hr, add_comm, mul_comm, mul_left_comm, mul_assoc] using this.symm
    have hr_lt : r < 3 := Nat.mod_lt _ (by decide)
    -- use the known order `3` of `2` modulo `7`
    have hpow : (2 ^ (3 * q)) ≡ (1 : ℕ) [MOD 7] := by
      have := (h23.pow q)
      simpa [Nat.pow_mul] using this
    have hpow_mul : (2 ^ n) ≡ (2 ^ r) [MOD 7] := by
      -- rewrite `2 ^ n` using `hn_eq`
      have : (2 ^ (3 * q + r)) ≡ (2 ^ (3 * q)) * (2 ^ r) [MOD 7] := by
        simpa [Nat.pow_add] using (Nat.ModEq.refl _).mul_right (2 ^ r)
      have : (2 ^ n) ≡ (2 ^ (3 * q)) * (2 ^ r) [MOD 7] := by
        simpa [hn_eq] using this
      have : (2 ^ n) ≡ (1 : ℕ) * (2 ^ r) [MOD 7] := by
        simpa [hpow] using this
      simpa using this
    have hrr : (2 ^ r) ≡ (1 : ℕ) [MOD 7] :=
      (hpow_mul.symm.trans hmod)
    -- now analyse the possible values of `r`
    have : r = 0 := by
      have hcases : r = 0 ∨ r = 1 ∨ r = 2 := by
        have : r < 3 := hr_lt
        interval_cases r using this
      rcases hcases with h0 | h1 | h2
      · exact h0
      · have : (2 ^ (1 : ℕ)) % 7 = 2 := by norm_num
        have : (2 ^ (1 : ℕ)) ≡ (1 : ℕ) [MOD 7] := by
          simpa [Nat.ModEq] using congrArg (fun t => Nat.ModEq t 1 7) (by rfl)
        have : False := by
          have : (2 : ℕ) ≡ (1 : ℕ) [MOD 7] := by
            simpa [pow_one] using hrr
          have : (2 : ℕ) % 7 = 1 % 7 := (Nat.ModEq).mp this
          linarith
        cases this
      · have : (2 ^ (2 : ℕ)) % 7 = 4 := by norm_num
        have : (2 ^ (2 : ℕ)) ≡ (1 : ℕ) [MOD 7] := by
          simpa [pow_two] using hrr
        have : False := by
          have : (4 : ℕ) % 7 = 1 % 7 := (Nat.ModEq).mp this
          linarith
        cases this
    -- conclude `3 | n`
    refine ⟨q, ?_⟩
    have : n = 3 * q + r := hn_eq
    simpa [this, hr] using congrArg (fun t => t) (by rw [hr]; rfl)
  · rintro ⟨k, rfl⟩
    -- use the known order to get the divisibility
    have : (2 : ℕ) ^ (3 * k) ≡ (1 : ℕ) [MOD 7] := by
      have := (h23.pow k)
      simpa [Nat.pow_mul] using this
    exact (Nat.modEq_iff_dvd).mp this

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  intro h
  have hmod : (2 ^ n) ≡ (-1 : ℕ) [MOD 7] :=
    (Nat.modEq_iff_dvd).mpr h
  have h23 : (2 : ℕ) ^ 3 ≡ (1 : ℕ) [MOD 7] := by
    norm_num
  -- write `n = 3 * q + r` with `r < 3`
  set q := n / 3 with hq
  set r := n % 3 with hr
  have hn_eq : n = 3 * q + r := by
    have := Nat.mod_add_div n 3
    simpa [hq, hr, add_comm, mul_comm, mul_left_comm, mul_assoc] using this.symm
  have hr_lt : r < 3 := Nat.mod_lt _ (by decide)
  have hpow : (2 ^ (3 * q)) ≡ (1 : ℕ) [MOD 7] := by
    have := (h23.pow q)
    simpa [Nat.pow_mul] using this
  have hpow_mul : (2 ^ n) ≡ (2 ^ r) [MOD 7] := by
    have : (2 ^ n) ≡ (2 ^ (3 * q)) * (2 ^ r) [MOD 7] := by
      simpa [hn_eq, Nat.pow_add] using (Nat.ModEq.refl _).mul_right (2 ^ r)
    have : (2 ^ n) ≡ (1 : ℕ) * (2 ^ r) [MOD 7] := by
      simpa [hpow] using this
    simpa using this
  have : (2 ^ r) ≡ (-1 : ℕ) [MOD 7] := (hpow_mul.symm.trans hmod)
  have : r = 0 ∨ r = 1 ∨ r = 2 := by
    have : r < 3 := hr_lt
    interval_cases r using this
  rcases this with h0 | h1 | h2
  · -- r = 0, then `2 ^ r = 1`, contradicting `1 ≡ -1`
    have : (1 : ℕ) ≡ (-1 : ℕ) [MOD 7] := by simpa [h0] using this
    have : (1 : ℕ) % 7 = (6 : ℕ) % 7 := (Nat.ModEq).mp this
    norm_num at this
  · -- r = 1, then `2 ≡ -1` impossible
    have : (2 : ℕ) ≡ (-1 : ℕ) [MOD 7] := by simpa [h1] using this
    have : (2 : ℕ) % 7 = (6 : ℕ) % 7 := (Nat.ModEq).mp this
    norm_num at this
  · -- r = 2, then `4 ≡ -1` impossible
    have : (4 : ℕ) ≡ (-1 : ℕ) [MOD 7] := by simpa [h2, pow_two] using this
    have : (4 : ℕ) % 7 = (6 : ℕ) % 7 := (Nat.ModEq).mp this
    norm_num at this
