import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

open Nat

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  -- the useful congruence `2^3 ≡ 1 (mod 7)`
  have h3 : (2 : ℕ) ^ 3 ≡ 1 [MOD 7] := by
    dsimp [ModEq]
    norm_num
  constructor
  · intro h7
    -- from the divisibility we get a congruence
    have hmod : (2 : ℕ) ^ n ≡ 1 [MOD 7] := (Nat.ModEq.of_dvd h7)
    -- we will compare the exponent modulo `3`
    have hpow :
        (2 : ℕ) ^ (3 * (n / 3)) ≡ (1 : ℕ) [MOD 7] := by
      have := (Nat.ModEq.pow h3 (n / 3))
      simpa [pow_mul] using this
    have htotal :
        (2 : ℕ) ^ n ≡ 2 ^ (n % 3) [MOD 7] := by
      -- rewrite `n` as `3 * (n / 3) + n % 3`
      have hn : n = 3 * (n / 3) + n % 3 := by
        have := Nat.mod_add_div n 3
        -- `Nat.mod_add_div` gives `n % 3 + 3 * (n / 3) = n`
        simpa [Nat.add_comm, Nat.mul_comm] using this.symm
      -- now use `pow_add` and the previous congruence
      calc
        (2 : ℕ) ^ n
            = (2 : ℕ) ^ (3 * (n / 3) + n % 3) := by simpa [hn]
        _ = (2 : ℕ) ^ (3 * (n / 3)) * 2 ^ (n % 3) := by
              simpa [pow_add] using rfl
        _ ≡ 1 * 2 ^ (n % 3) [MOD 7] := by
              exact (Nat.ModEq.mul_right _ hpow)
        _ = 2 ^ (n % 3) := by simp
    have hfinal : (2 : ℕ) ^ (n % 3) ≡ 1 [MOD 7] := by
      exact (htotal.symm.trans hmod)
    -- analyse the possible values of `n % 3`
    have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
      have hlt : n % 3 < 3 := Nat.mod_lt _ (by decide)
      interval_cases (n % 3) using hlt <;> tauto
    rcases hcases with h0 | h1 | h2
    · -- the wanted case
      exact Nat.dvd_of_mod_eq_zero h0
    · -- contradiction with `hfinal`
      have : (2 ^ (n % 3)) % 7 = 1 := by
        dsimp [ModEq] at hfinal
        simpa [h1] using hfinal
      have : (2 : ℕ) % 7 = 1 := by simpa [h1] using this
      norm_num at this
    · -- another contradiction
      have : (2 ^ (n % 3)) % 7 = 1 := by
        dsimp [ModEq] at hfinal
        simpa [h2] using hfinal
      have : (4 : ℕ) % 7 = 1 := by simpa [h2] using this
      norm_num at this
  · intro h3d
    rcases h3d with ⟨k, hk⟩
    -- `n = 3 * k`, so `2^n - 1` is divisible by `7`
    have : (2 : ℕ) ^ (3 * k) - 1 ∣ 7 := by
      -- use the congruence `2^3 ≡ 1`
      have hpow : (2 : ℕ) ^ (3 * k) ≡ 1 [MOD 7] := by
        have := (Nat.ModEq.pow h3 k)
        simpa [pow_mul] using this
      have : (2 : ℕ) ^ (3 * k) - 1 ≡ 0 [MOD 7] := by
        dsimp [ModEq] at hpow
        simpa [hpow] using rfl
      exact (Nat.ModEq.dvd_iff_dvd_sub _ _).mp (by
        dsimp [ModEq] at hpow
        exact (Nat.ModEq.of_dvd ?_))
    -- more directly, we can just use `Nat.ModEq` to get the required divisibility
    have hmod : (2 : ℕ) ^ (3 * k) ≡ 1 [MOD 7] := by
      have := (Nat.ModEq.pow h3 k)
      simpa [pow_mul] using this
    exact (Nat.ModEq.of_dvd (by
      dsimp [ModEq] at hmod
      exact hmod))
    -- finally rewrite using `n = 3 * k`
    simpa [hk, mul_comm] 

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬ 7 ∣ 2 ^ n + 1 := by
  intro h
  -- from the divisibility we get a congruence
  have hmod : (2 : ℕ) ^ n ≡ 6 [MOD 7] := by
    have : 7 ∣ 2 ^ n + 1 := h
    have : 7 ∣ 2 ^ n - (−1) := by
      simpa [sub_eq, add_comm, add_left_neg] using this
    exact (Nat.ModEq.of_dvd this)
  -- as before, reduce the exponent modulo `3`
  have h3 : (2 : ℕ) ^ 3 ≡ 1 [MOD 7] := by
    dsimp [ModEq]; norm_num
  have hpow :
      (2 : ℕ) ^ (3 * (n / 3)) ≡ (1 : ℕ) [MOD 7] := by
    have := (Nat.ModEq.pow h3 (n / 3))
    simpa [pow_mul] using this
  have htotal :
      (2 : ℕ) ^ n ≡ 2 ^ (n % 3) [MOD 7] := by
    have hn : n = 3 * (n / 3) + n % 3 := by
      have := Nat.mod_add_div n 3
      simpa [Nat.add_comm, Nat.mul_comm] using this.symm
    calc
      (2 : ℕ) ^ n
          = (2 : ℕ) ^ (3 * (n / 3) + n % 3) := by simpa [hn]
      _ = (2 : ℕ) ^ (3 * (n / 3)) * 2 ^ (n % 3) := by
            simpa [pow_add] using rfl
      _ ≡ 1 * 2 ^ (n % 3) [MOD 7] := by
            exact (Nat.ModEq.mul_right _ hpow)
      _ = 2 ^ (n % 3) := by simp
  have hfinal : (2 : ℕ) ^ (n % 3) ≡ 6 [MOD 7] :=
    (htotal.symm.trans hmod)
  -- analyse the possible remainders
  have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
    have hlt : n % 3 < 3 := Nat.mod_lt _ (by decide)
    interval_cases (n % 3) using hlt <;> tauto
  rcases hcases with h0 | h1 | h2
  · -- remainder `0` gives `2^0 ≡ 1`, contradiction
    have : (2 ^ (n % 3)) % 7 = 6 := by
      dsimp [ModEq] at hfinal
      simpa [h0] using hfinal
    have : (1 : ℕ) % 7 = 6 := by simpa [h0] using this
    norm_num at this
  · -- remainder `1` gives `2 ≡ 6`, impossible
    have : (2 ^ (n % 3)) % 7 = 6 := by
      dsimp [ModEq] at hfinal
      simpa [h1] using hfinal
    have : (2 : ℕ) % 7 = 6 := by simpa [h1] using this
    norm_num at this
  · -- remainder `2` gives `4 ≡ 6`, impossible
    have : (2 ^ (n % 3)) % 7 = 6 := by
      dsimp [ModEq] at hfinal
      simpa [h2] using hfinal
    have : (4 : ℕ) % 7 = 6 := by simpa [h2] using this
    norm_num at this
