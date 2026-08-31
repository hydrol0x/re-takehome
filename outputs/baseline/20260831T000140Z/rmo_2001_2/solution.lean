import Mathlib.Data.Nat.Prime
import Mathlib.Tactic

open Nat

/-- Main theorem: characterisation of primes `p q` such that `p^2 + 7*p*q + q^2` is a square. -/
theorem rmo_2001_2 (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
    (∃ m : ℕ, p ^ 2 + 7 * p * q + q ^ 2 = m ^ 2) ↔
      (p = q ∨ (p = 3 ∧ q = 11) ∨ (p = 11 ∧ q = 3)) := by
  constructor
  · intro h
    rcases h with ⟨m, hm⟩
    have h₁ : (p + q) ^ 2 + 5 * p * q = m ^ 2 := by
      have : p ^ 2 + 7 * p * q + q ^ 2 = (p + q) ^ 2 + 5 * p * q := by
        ring
      simpa [this] using hm
    -- set the two factors
    set a := m - (p + q) with ha
    set b := m + (p + q) with hb
    have hab : a * b = 5 * p * q := by
      have : (m - (p + q)) * (m + (p + q)) = m ^ 2 - (p + q) ^ 2 := by
        ring
      have : a * b = m ^ 2 - (p + q) ^ 2 := by
        simpa [ha, hb] using this
      have : m ^ 2 - (p + q) ^ 2 = 5 * p * q := by
        have : (p + q) ^ 2 + 5 * p * q = m ^ 2 := h₁
        linarith
      simpa [this] using this
    have hpos : 0 < a := by
      have : (p + q) ^ 2 < (p + q) ^ 2 + 5 * p * q := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_add_right _ _)
      have : (p + q) ^ 2 < m ^ 2 := by simpa [h₁] using this
      have : p + q < m := Nat.lt_of_pow_lt_pow (Nat.succ_pos _) this
      have : m - (p + q) > 0 := Nat.sub_pos_of_lt this
      simpa [ha] using this
    have hle : a ≤ b := by
      have : m - (p + q) ≤ m + (p + q) := Nat.sub_le_iff_le_add.mpr (Nat.le_add_left _ _)
      simpa [ha, hb] using this
    have hdiff : b - a = 2 * (p + q) := by
      have : (m + (p + q)) - (m - (p + q)) = 2 * (p + q) := by
        ring
      simpa [hb, ha] using this
    -- enumerate the possible factorizations of `5 * p * q`
    have hdiv : a ∣ 5 * p * q := ⟨b, hab.symm⟩
    have hprime : p ≠ 1 ∧ q ≠ 1 := ⟨hp.ne_one, hq.ne_one⟩
    have h5 : 5 ≠ 1 := by decide
    have hcases : a = 1 ∨ a = 5 ∨ a = p ∨ a = q ∨ a = 5 * p ∨ a = 5 * q ∨ a = p * q ∨ a = 5 * p * q := by
      have : a ∈ (Finset.factors (5 * p * q)).toList := by
        have : a ∣ 5 * p * q := hdiv
        exact Nat.dvd_of_mem_factors this
      rcases a with _ | a
      · exact False.elim (Nat.not_lt_zero _ (Nat.lt_of_lt_of_le (Nat.succ_pos _) (Nat.le_of_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_one)))))
      ·
        have hmem : a ∈ (Finset.factors (5 * p * q)).toList := by
          have : a ∣ 5 * p * q := hdiv
          exact Nat.dvd_of_mem_factors this
        have hlist : (Finset.factors (5 * p * q)).toList = [1,5,p,q,5*p,5*q,p*q,5*p*q] := by
          have hp' : p.Prime := hp
          have hq' : q.Prime := hq
          have : (5 * p * q).factors = [5,p,q] := by
            simpa [Nat.factors_mul, Nat.factors_prime hp', Nat.factors_prime hq', Nat.factors_prime (by decide : Nat.Prime 5)] using rfl
          sorry
        sorry
    -- From the possible values of `a` we deduce the required equalities.
    have : p = q ∨ (p = 3 ∧ q = 11) ∨ (p = 11 ∧ q = 3) := by
      -- we now check each case
      rcases hcases with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
      · -- a = 1
        have : 1 * b = 5 * p * q := hab
        have hbpos : b = 5 * p * q := by simpa [h1] using this
        have : b - 1 = 2 * (p + q) := by simpa [h1] using hdiff
        have : 5 * p * q - 1 = 2 * (p + q) := by simpa [hbpos] using this
        have : 5 * p * q = 2 * (p + q) + 1 := by linarith
        have hmod : (5 * p * q) % 2 = 1 % 2 := by
          simpa [Nat.mod_eq_of_lt (by decide : 1 < 2)] using congrArg (fun n => n % 2) this
        have : (5 * p * q) % 2 = 1 := by simpa using hmod
        have : (p * q) % 2 = 1 := by
          have : (5 % 2) = 1 := by decide
          simpa [Nat.mul_mod, this] using this
        have hpodd : p % 2 = 1 := by
          have : (p * q) % 2 = (p % 2) * (q % 2) % 2 := by
            simpa [Nat.mul_mod] using rfl
          have : (p % 2) * (q % 2) % 2 = 1 := by simpa [this] using this
          have hqodd : q % 2 = 1 := by
            have : (p % 2) = 1 ∨ (p % 2) = 0 := by decide
            cases this with
            | inl hp1 => exact ?_
            | inr hp0 => ?_
          sorry
        sorry
      · -- a = 5
        sorry
      · -- a = p
        sorry
      · -- a = q
        sorry
      · -- a = 5 * p
        sorry
      · -- a = 5 * q
        sorry
      · -- a = p * q
        sorry
      · -- a = 5 * p * q
        sorry
    exact this
  · intro h
    rcases h with h | h | h
    · rcases h with rfl
      refine ⟨p + 5 * p, ?_⟩
      have : p ^ 2 + 7 * p * p + p ^ 2 = (p + 5 * p) ^ 2 := by
        ring
      simpa [pow_two] using this
    · rcases h with ⟨hp3, hq11⟩
      subst hp3
      subst hq11
      refine ⟨34, ?_⟩
      norm_num
    · rcases h with ⟨hp11, hq3⟩
      subst hp11
      subst hq3
      refine ⟨34, ?_⟩
      norm_num
