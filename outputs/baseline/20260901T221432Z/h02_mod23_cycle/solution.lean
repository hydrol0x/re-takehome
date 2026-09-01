import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic
import Mathlib.Tactic.IntervalCases

open Nat

/-- (a): `23 ∣ 2 ^ n - 1` iff `11 ∣ n`, for positive `n`. -/
theorem h02_a (n : ℕ) (hn : 0 < n) : 23 ∣ 2 ^ n - 1 ↔ 11 ∣ n := by
  -- auxiliary: for `r < 11`, `2 ^ r ≡ 1 [MOD 23]` implies `r = 0`
  have h_aux : ∀ r : ℕ, r < 11 → (2 ^ r) ≡ (1 : ℕ) [MOD 23] → r = 0 := by
    intro r hr hmod
    interval_cases r <;> try {simp [Nat.ModEq] at hmod}
    all_goals
      try {simp [Nat.ModEq] at hmod}
      all_goals
        try {contradiction}
  -- `2 ^ 11 ≡ 1 [MOD 23]`
  have h11 : (2 ^ 11 : ℕ) ≡ 1 [MOD 23] := by
    norm_num
  constructor
  · intro hdiv
    -- turn divisibility into a `ModEq`
    have hmod : (2 ^ n) ≡ (1 : ℕ) [MOD 23] := by
      have : (2 ^ n - 1) % 23 = 0 := (Nat.dvd_iff_mod_eq_zero).mp hdiv
      dsimp [Nat.ModEq] at *
      have : (2 ^ n) % 23 = 1 % 23 := by
        have := Nat.mod_eq_of_lt (Nat.mod_lt (2 ^ n) (by decide))
        simpa [Nat.sub_eq, this] using this
      simpa [Nat.ModEq] using this
    -- write `n = 11 * q + r`
    obtain ⟨q, r, hqr⟩ := Nat.mod_mul_left_mod n 11
    have hnr : n = 11 * q + r := by
      have := Nat.mod_add_div n 11
      simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this.symm
    have hr_lt : r < 11 := Nat.mod_lt _ (by decide)
    -- use the decomposition of the exponent
    have : (2 ^ (11 * q + r)) ≡ (1 : ℕ) [MOD 23] := by
      simpa [hnr] using hmod
    have : ((2 ^ 11) ^ q * 2 ^ r) ≡ (1 : ℕ) [MOD 23] := by
      simpa [pow_add, pow_mul] using this
    have hpow : ((2 ^ 11) ^ q) ≡ (1 : ℕ) [MOD 23] := by
      simpa [h11] using (h11.pow q)
    have : (2 ^ r) ≡ (1 : ℕ) [MOD 23] := by
      have := (Nat.ModEq.mul_left_cancel_iff (Nat.coprime_one_left _)).mp
        (by
          have := this
          simpa [hpow, one_mul] using this)
      exact this
    exact ⟨q, by
      have := h_aux r hr_lt this
      simpa [this, Nat.mul_comm]⟩
  · intro hdiv
    rcases hdiv with ⟨k, hk⟩
    have : (2 ^ (11 * k)) ≡ (1 : ℕ) [MOD 23] := by
      simpa [hk, pow_mul] using (h11.pow k)
    have : (2 ^ n) ≡ (1 : ℕ) [MOD 23] := by
      simpa [hk, pow_mul] using this
    exact (Nat.dvd_iff_mod_eq_zero).mpr (by
      dsimp [Nat.ModEq] at this
      simpa [Nat.sub_eq, Nat.mod_eq_of_lt (Nat.mod_lt (2 ^ n) (by decide))] using this)

/-- (b): no positive `n` has `23 ∣ 2 ^ n + 1`. -/
theorem h02_b (n : ℕ) (hn : 0 < n) : ¬23 ∣ 2 ^ n + 1 := by
  intro hdiv
  have hmod : (2 ^ n) ≡ (−1 : ℕ) [MOD 23] := by
    have : (2 ^ n + 1) % 23 = 0 := (Nat.dvd_iff_mod_eq_zero).mp hdiv
    dsimp [Nat.ModEq] at *
    have : (2 ^ n) % 23 = (23 - 1) % 23 := by
      simpa [Nat.add_mod, Nat.mod_eq_of_lt (Nat.mod_lt (2 ^ n) (by decide)), Nat.mod_self] using this
    simpa [Nat.ModEq] using this
  have hpow11 : (2 ^ 11 : ℕ) ≡ 1 [MOD 23] := by
    norm_num
  have horder : (2 : ℕ) ≡ 0 [MOD 23] ∨ (2 : ℕ) ≡ 1 [MOD 23] ∨ (2 : ℕ) ≡ 2 [MOD 23] ∨
                (2 : ℕ) ≡ 3 [MOD 23] ∨ (2 : ℕ) ≡ 4 [MOD 23] ∨ (2 : ℕ) ≡ 5 [MOD 23] ∨
                (2 : ℕ) ≡ 6 [MOD 23] ∨ (2 : ℕ) ≡ 7 [MOD 23] ∨ (2 : ℕ) ≡ 8 [MOD 23] ∨
                (2 : ℕ) ≡ 9 [MOD 23] ∨ (2 : ℕ) ≡ 10 [MOD 23] ∨ (2 : ℕ) ≡ 11 [MOD 23] ∨
                (2 : ℕ) ≡ 12 [MOD 23] ∨ (2 : ℕ) ≡ 13 [MOD 23] ∨ (2 : ℕ) ≡ 14 [MOD 23] ∨
                (2 : ℕ) ≡ 15 [MOD 23] ∨ (2 : ℕ) ≡ 16 [MOD 23] ∨ (2 : ℕ) ≡ 17 [MOD 23] ∨
                (2 : ℕ) ≡ 18 [MOD 23] ∨ (2 : ℕ) ≡ 19 [MOD 23] ∨ (2 : ℕ) ≡ 20 [MOD 23] ∨
                (2 : ℕ) ≡ 21 [MOD 23] ∨ (2 : ℕ) ≡ 22 [MOD 23] := by
    decide
  have : False := by
    have : (2 ^ (2 * 11)) ≡ (1 : ℕ) [MOD 23] := by
      simpa using (hpow11.pow 2)
    have : (2 ^ n) ≡ (−1 : ℕ) [MOD 23] := hmod
    have : (2 ^ (2 * 11)) ≡ (−1 : ℕ) [MOD 23] := by
      simpa [pow_mul] using this
    have : (1 : ℕ) ≡ (−1 : ℕ) [MOD 23] := by
      simpa [this] using (Nat.ModEq.trans (by simpa using (hpow11.pow 2)) this)
    have : (2 : ℕ) ≡ (0 : ℕ) [MOD 23] := by
      have := this
      norm_num at this
    exact horder.elim (fun h => h.elim) (fun h => h.elim) (fun h => h.elim) (fun h => h.elim)
  exact this
