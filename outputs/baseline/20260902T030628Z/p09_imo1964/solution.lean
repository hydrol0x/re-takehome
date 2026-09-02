import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  -- rewrite the divisibility in terms of `ModEq`
  have h7 : (7 : ℕ) ≠ 0 := by decide
  have hmod_eq (a b : ℕ) : (7 ∣ a - b) ↔ a ≡ b [MOD 7] := by
    constructor
    · intro h
      have : (a - b) % 7 = 0 := Nat.mod_eq_zero_of_dvd h
      have : (a % 7) = (b % 7) := by
        have := congrArg (fun x => (x + b) % 7) this
        simpa [Nat.sub_add_cancel (Nat.le_of_lt (Nat.lt_of_lt_of_le hn (Nat.le_of_lt (Nat.pow_pos (by decide) n)))),
               Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
               Nat.mod_add_mod, Nat.mod_self] using this
      exact this
    · intro h
      have : (a - b) % 7 = 0 := by
        have : a % 7 = b % 7 := h
        have := congrArg (fun x => (x - b % 7) % 7) this
        simpa [Nat.sub_mod, Nat.mod_self, Nat.mod_eq_of_lt (by decide : b % 7 < 7)] using this
      exact Nat.dvd_of_mod_eq_zero this
  -- the key congruence `2^3 ≡ 1 [MOD 7]`
  have h23 : (2 : ℕ) ^ 3 ≡ (1 : ℕ) [MOD 7] := by
    dsimp [Nat.ModEq]; norm_num
  -- from it we get `2^(3*k) ≡ 1 [MOD 7]`
  have hpow (k : ℕ) : (2 : ℕ) ^ (3 * k) ≡ (1 : ℕ) [MOD 7] := by
    simpa [pow_mul] using (h23.pow k)
  -- now prove the equivalence
  constructor
  · intro h
    have hmod : (2 ^ n) ≡ (1 : ℕ) [MOD 7] := (hmod_eq _ _).1 h
    -- write `n = 3 * (n / 3) + n % 3`
    have hdiv : n = (n / 3) * 3 + n % 3 := (Nat.div_mod_eq_mul_add_mod n 3).symm
    -- replace `n` in the congruence
    have : (2 : ℕ) ^ ((n / 3) * 3 + n % 3) ≡ (1 : ℕ) [MOD 7] := by
      simpa [hdiv] using hmod
    -- split the power
    have : ((2 : ℕ) ^ ((n / 3) * 3) * (2 : ℕ) ^ (n % 3)) ≡ (1 : ℕ) [MOD 7] := by
      simpa [pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
    -- use the fact that the first factor is `1` modulo `7`
    have hfirst : (2 : ℕ) ^ ((n / 3) * 3) ≡ (1 : ℕ) [MOD 7] := by
      simpa [Nat.mul_comm] using hpow (n / 3)
    have : (2 : ℕ) ^ (n % 3) ≡ (1 : ℕ) [MOD 7] := by
      have := (Nat.ModEq.mul_left_cancel_iff (a:= (2 : ℕ) ^ ((n / 3) * 3)) (b:=1) (c:= (2 : ℕ) ^ (n % 3))
                (by
                  have : ((2 : ℕ) ^ ((n / 3) * 3)) % 7 = 1 % 7 := (hfirst.eq)
                  simpa [Nat.mod_eq_of_lt (by decide : 1 < 7)] using this))
      simpa [Nat.ModEq, Nat.mul_comm] using this
    -- now analyse `n % 3`
    have hlt : n % 3 < 3 := Nat.mod_lt _ (by decide)
    interval_cases (n % 3) using hlt with
    | zero =>
        exact ⟨n / 3, by
          have : n = 3 * (n / 3) := by
            simpa [Nat.mod_eq_zero_of_dvd (Nat.dvd_of_mod_eq_zero (by simpa [zero] using hlt))] using hdiv
          simpa [this, Nat.mul_comm]⟩
    | succ (succ 0) => -- case 2
        have : (2 : ℕ) ^ 2 % 7 = 4 := by norm_num
        have : (2 : ℕ) ^ (n % 3) % 7 = 4 := by simpa using this
        have : (2 : ℕ) ^ (n % 3) % 7 = 1 := by
          simpa [Nat.ModEq] using this
        linarith
    | succ 0 => -- case 1
        have : (2 : ℕ) ^ 1 % 7 = 2 := by norm_num
        have : (2 : ℕ) ^ (n % 3) % 7 = 2 := by simpa using this
        have : (2 : ℕ) ^ (n % 3) % 7 = 1 := by
          simpa [Nat.ModEq] using this
        linarith
  · intro h
    rcases h with ⟨k, hk⟩
    have : (2 : ℕ) ^ n ≡ (1 : ℕ) [MOD 7] := by
      have : (2 : ℕ) ^ (3 * k) ≡ (1 : ℕ) [MOD 7] := hpow k
      simpa [hk, Nat.mul_comm] using this
    exact (hmod_eq _ _).2 this

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  intro h
  have hmod : (2 ^ n) ≡ (−1 : ℕ) [MOD 7] := by
    have : (2 ^ n + 1) % 7 = 0 := Nat.mod_eq_zero_of_dvd h
    have : (2 ^ n) % 7 = (7 - 1) % 7 := by
      have := congrArg (fun x => (x - 1) % 7) this
      simpa [Nat.add_sub_cancel, Nat.mod_self, Nat.mod_eq_of_lt (by decide : 1 < 7)] using this
    simpa [Nat.ModEq, Nat.mod_eq_of_lt (by decide : 6 < 7)] using this
  have hpow : (2 : ℕ) ^ (n % 3) ≡ (−1 : ℕ) [MOD 7] := by
    -- as in part (a) we reduce the exponent modulo 3
    have hdecomp : n = (n / 3) * 3 + n % 3 := (Nat.div_mod_eq_mul_add_mod n 3).symm
    have : (2 : ℕ) ^ n ≡ (2 : ℕ) ^ (n % 3) [MOD 7] := by
      have hfirst : (2 : ℕ) ^ ((n / 3) * 3) ≡ (1 : ℕ) [MOD 7] := by
        simpa [Nat.mul_comm] using (by
          have := (by
            have h23 : (2 : ℕ) ^ 3 ≡ (1 : ℕ) [MOD 7] := by
              dsimp [Nat.ModEq]; norm_num
            exact (h23.pow (n / 3)))
          simpa [pow_mul] using this)
      have : (2 : ℕ) ^ n ≡ (2 : ℕ) ^ ((n / 3) * 3) * (2 : ℕ) ^ (n % 3)) [MOD 7] := by
        simpa [hdecomp, pow_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using (Nat.ModEq.rfl : (2 : ℕ) ^ n ≡ (2 : ℕ) ^ n [MOD 7])
      simpa [Nat.ModEq] using (Nat.ModEq.trans this (Nat.ModEq.mul_left_cancel_iff hfirst (by decide)).symm)
    simpa using (Nat.ModEq.trans this hmod)
  have hlt : n % 3 < 3 := Nat.mod_lt _ (by decide)
  interval_cases (n % 3) using hlt with
  | zero =>
      have : (2 : ℕ) ^ 0 % 7 = 1 := by norm_num
      have : (2 : ℕ) ^ (n % 3) % 7 = 1 := by simpa using this
      have : (2 : ℕ) ^ (n % 3) % 7 = 6 := by
        simpa [Nat.ModEq] using hpow
      linarith
  | succ 0 =>
      have : (2 : ℕ) ^ 1 % 7 = 2 := by norm_num
      have : (2 : ℕ) ^ (n % 3) % 7 = 2 := by simpa using this
      have : (2 : ℕ) ^ (n % 3) % 7 = 6 := by
        simpa [Nat.ModEq] using hpow
      linarith
  | succ (succ 0) =>
      have : (2 : ℕ) ^ 2 % 7 = 4 := by norm_num
      have : (2 : ℕ) ^ (n % 3) % 7 = 4 := by simpa using this
      have : (2 : ℕ) ^ (n % 3) % 7 = 6 := by
        simpa [Nat.ModEq] using hpow
      linarith
