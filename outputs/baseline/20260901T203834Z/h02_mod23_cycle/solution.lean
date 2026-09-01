import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

open Nat

/-- (a): `23 ∣ 2 ^ n - 1` iff `11 ∣ n`, for positive `n`. -/
theorem h02_a (n : ℕ) (hn : 0 < n) : 23 ∣ 2 ^ n - 1 ↔ 11 ∣ n := by
  -- rewrite the divisibility condition as a `ModEq`
  have h23 : (23 : ℕ) ≠ 0 := by decide
  have hdiv_mod : (23 ∣ 2 ^ n - 1) ↔ (2 ^ n) ≡ 1 [MOD 23] := by
    simpa using (Nat.ModEq.dvd_iff_modEq h23 (a := 2 ^ n) (b := 1))
  -- the order of `2` modulo `23` is `11`
  have horder : (2 : ℕ) ^ 11 ≡ 1 [MOD 23] := by norm_num
  -- a useful periodicity lemma
  have hperiod (k : ℕ) : (2 : ℕ) ^ (k + 11) ≡ (2 : ℕ) ^ k [MOD 23] := by
    have := (Nat.ModEq.mul_left (2 ^ k) horder)
    simpa [pow_add, mul_comm] using this
  -- reduction of the exponent modulo `11`
  have hreduce : (2 : ℕ) ^ n ≡ (2 : ℕ) ^ (n % 11) [MOD 23] := by
    -- write `n = 11 * (n / 11) + n % 11`
    have hdecomp : n = 11 * (n / 11) + n % 11 := by
      simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (Nat.mod_mul_left_div_self n 11).symm
    -- rewrite the power using this decomposition
    calc
      (2 : ℕ) ^ n
          = (2 : ℕ) ^ (11 * (n / 11) + n % 11) := by simpa [hdecomp]
      _ = (2 ^ (11 * (n / 11))) * (2 ^ (n % 11)) := by
            simpa [pow_add] using rfl
      _ = ((2 ^ 11) ^ (n / 11)) * (2 ^ (n % 11)) := by
            simpa [pow_mul] using rfl
      _ ≡ (1 ^ (n / 11)) * (2 ^ (n % 11)) [MOD 23] := by
            exact (horder.pow (n / 11)).mul_left _
      _ = (2 ^ (n % 11)) [MOD 23] := by
            simpa [one_pow, one_mul] using rfl
  constructor
  · intro hdiv
    have hmod : (2 ^ n) ≡ 1 [MOD 23] := (hdiv_mod.mp hdiv)
    have hmod' : (2 ^ (n % 11)) ≡ 1 [MOD 23] := (hreduce.trans hmod).symm
    -- analyse the remainder `r = n % 11`
    have hlt : n % 11 < 11 := Nat.mod_lt _ (by decide : 0 < 11)
    have : n % 11 = 0 := by
      interval_cases (n % 11) using hlt
      · rfl
      all_goals
        have : (2 ^ (n % 11)) % 23 ≠ 1 := by decide
        have : (2 ^ (n % 11)) % 23 = 1 := by
          simpa [Nat.ModEq] using hmod'
        exact (this this).elim
    exact ⟨n / 11, by
      have : n = 11 * (n / 11) := by
        simpa [Nat.mod_mul_left_div_self, this] using (Nat.mod_mul_left_div_self n 11).symm
      simpa [this, mul_comm]⟩
  · rintro ⟨k, hk⟩
    have : (2 : ℕ) ^ (11 * k) ≡ 1 [MOD 23] := by
      simpa [hk, pow_mul] using (horder.pow k)
    have : (2 ^ n) ≡ 1 [MOD 23] := by
      have hdecomp : n = 11 * k := by simpa [hk] using rfl
      simpa [hdecomp] using this
    exact hdiv_mod.mpr this

/-- (b): no positive `n` has `23 ∣ 2 ^ n + 1`. -/
theorem h02_b (n : ℕ) (hn : 0 < n) : ¬23 ∣ 2 ^ n + 1 := by
  have h23 : (23 : ℕ) ≠ 0 := by decide
  have hdiv_mod : (23 ∣ 2 ^ n + 1) ↔ (2 ^ n) ≡ (-1 : ℕ) [MOD 23] := by
    simpa [add_comm] using (Nat.ModEq.dvd_iff_modEq h23 (a := 2 ^ n) (b := (23 - 1)))
  intro h
  have hmod : (2 ^ n) ≡ (-1 : ℕ) [MOD 23] := (hdiv_mod.mp h)
  -- from part (a) we know the order of `2` modulo `23` is `11`, which is odd,
  -- hence `2 ^ n` can never be congruent to `-1`.
  have horder : (2 : ℕ) ^ 11 ≡ 1 [MOD 23] := by norm_num
  have hperiod (k : ℕ) : (2 : ℕ) ^ (k + 11) ≡ (2 : ℕ) ^ k [MOD 23] := by
    have := (Nat.ModEq.mul_left (2 ^ k) horder)
    simpa [pow_add, mul_comm] using this
  have hreduce : (2 : ℕ) ^ n ≡ (2 : ℕ) ^ (n % 11) [MOD 23] := by
    -- same reduction as in part (a)
    have hdecomp : n = 11 * (n / 11) + n % 11 := by
      simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        (Nat.mod_mul_left_div_self n 11).symm
    calc
      (2 : ℕ) ^ n
          = (2 : ℕ) ^ (11 * (n / 11) + n % 11) := by simpa [hdecomp]
      _ = (2 ^ (11 * (n / 11))) * (2 ^ (n % 11)) := by
            simpa [pow_add] using rfl
      _ = ((2 ^ 11) ^ (n / 11)) * (2 ^ (n % 11)) := by
            simpa [pow_mul] using rfl
      _ ≡ (1 ^ (n / 11)) * (2 ^ (n % 11)) [MOD 23] := by
            exact (horder.pow (n / 11)).mul_left _
      _ = (2 ^ (n % 11)) [MOD 23] := by
            simpa [one_pow, one_mul] using rfl
  have hmod' : (2 : ℕ) ^ (n % 11) ≡ (-1 : ℕ) [MOD 23] := (hreduce.trans hmod).symm
  have hlt : n % 11 < 11 := Nat.mod_lt _ (by decide : 0 < 11)
  have : False := by
