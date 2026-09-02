import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

open Nat

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  -- rewrite the divisibility condition as a ModEq
  have h7 : (7 ∣ 2 ^ n - 1) ↔ (2 ^ n) ≡ 1 [MOD 7] := by
    constructor
    · intro h
      exact (Nat.ModEq.dvd_iff).mpr h
    · intro h
      exact (Nat.ModEq.dvd_iff).mp h
  -- the key congruence `2^3 ≡ 1 [MOD 7]`
  have h23 : (2 ^ 3 : ℕ) ≡ 1 [MOD 7] := by norm_num
  -- auxiliary lemma: for any `k`, `2^(3*k) ≡ 1 [MOD 7]`
  have hpow3 (k : ℕ) : (2 ^ (3 * k) : ℕ) ≡ 1 [MOD 7] := by
    have := (Nat.ModEq.pow h23 k)
    simpa [pow_mul] using this
  -- auxiliary lemma: for any `k r`, `2^(3*k+r) ≡ 2^r [MOD 7]`
  have hdecomp (k r : ℕ) : (2 ^ (3 * k + r) : ℕ) ≡ 2 ^ r [MOD 7] := by
    have : (2 ^ (3 * k + r) : ℕ) = (2 ^ (3 * k)) * (2 ^ r) := by
      simpa [pow_add] using rfl
    have h1 : (2 ^ (3 * k) : ℕ) ≡ 1 [MOD 7] := hpow3 k
    have h2 : (2 ^ (3 * k) * 2 ^ r : ℕ) ≡ 1 * 2 ^ r [MOD 7] :=
      (Nat.ModEq.mul_left _ h1).trans (Nat.ModEq.mul_right _ (Nat.ModEq.refl _))
    simpa [this, one_mul] using h2
  constructor
  · intro h
    have hmod : (2 ^ n : ℕ) ≡ 1 [MOD 7] := (h7.mp h)
    -- write `n = 3 * q + r` with `r < 3`
    obtain ⟨q, r, hqr, hr⟩ := Nat.mod_mul_left_mod n 3
    have : (2 ^ n : ℕ) ≡ 2 ^ r [MOD 7] := by
      have := hdecomp q r
      simpa [hqr] using this
    have : (2 ^ r : ℕ) ≡ 1 [MOD 7] := (Nat.ModEq.trans this hmod)
    -- now analyse the possible values of `r`
    have : r = 0 := by
      have hlt : r < 3 := hr
      fin_cases r <;> try (simp [Nat.ModEq, Nat.mod_eq_of_lt] at this)
    exact ⟨r, this.symm⟩
  · rintro ⟨k, rfl⟩
    -- `n = 3 * k`, so the result follows from `hpow3`
    have : (2 ^ (3 * k) : ℕ) ≡ 1 [MOD 7] := hpow3 k
    exact (h7.mpr ((Nat.ModEq.dvd_iff).mpr this))

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  intro h
  have hmod : (2 ^ n : ℕ) ≡ (-1 : ℕ) [MOD 7] := by
    -- `7 ∣ 2^n + 1`  ↔  `2^n ≡ -1 [MOD 7]`
    have : (7 ∣ 2 ^ n + 1) ↔ (2 ^ n : ℕ) ≡ (-1 : ℕ) [MOD 7] := by
      constructor
      · intro h
        exact (Nat.ModEq.dvd_iff).mpr h
      · intro h
        exact (Nat.ModEq.dvd_iff).mp h
    exact (this.mp h)
  -- compute possible residues of `2^n` modulo 7
  have hpow3 : (2 ^ 3 : ℕ) ≡ 1 [MOD 7] := by norm_num
  obtain ⟨q, r, hqr, hr⟩ := Nat.mod_mul_left_mod n 3
  have hdecomp : (2 ^ n : ℕ) ≡ 2 ^ r [MOD 7] := by
    have := (by
      have := (Nat.ModEq.pow hpow3 q)
      simpa [pow_mul, hqr, pow_add] using this)
    simpa [hqr] using this
  have : (2 ^ r : ℕ) ≡ (-1 : ℕ) [MOD 7] := (Nat.ModEq.trans hdecomp hmod)
  have hr0 : r = 0 ∨ r = 1 ∨ r = 2 := by
    have : r < 3 := hr
    interval_cases r <;> tauto
  rcases hr0 with h0 | h1 | h2
  · -- r = 0, then `2^r = 1`, contradiction with `1 ≡ -1 [MOD 7]`
    have : (1 : ℕ) ≡ (-1 : ℕ) [MOD 7] := by simpa [h0] using this
    norm_num at this
  · -- r = 1, then `2^r = 2`, contradiction with `2 ≡ -1 [MOD 7]`
    have : (2 : ℕ) ≡ (-1 : ℕ) [MOD 7] := by simpa [h1] using this
    norm_num at this
  · -- r = 2, then `2^r = 4`, contradiction with `4 ≡ -1 [MOD 7]`
    have : (4 : ℕ) ≡ (-1 : ℕ) [MOD 7] := by simpa [h2] using this
    norm_num at this
