import Mathlib.Data.Nat.Prime
import Mathlib.Tactic

open Nat

/-- Auxiliary lemma: the only ways to write `5 * p * q` as a product `a * b` with
`b - a = 2 * (p + q)` and `p, q` prime are the trivial ones. -/
private lemma factor_cases (p q a b : ℕ) (hp : Prime p) (hq : Prime q)
    (hprod : a * b = 5 * p * q) (hdiff : b - a = 2 * (p + q)) :
    a = 1 ∧ b = 5 * p * q ∨
    a = 5 ∧ b = p * q ∨
    a = p ∧ b = 5 * q ∨
    a = q ∧ b = 5 * p ∨
    a = p * q ∧ b = 5 ∨
    a = 5 * p * q ∧ b = 1 := by
  have h5 : Prime 5 := prime_nat_of_mem_primes (by decide)
  have hdiv : a ∣ 5 * p * q := ⟨b, hprod.symm⟩
  rcases (Nat.dvd_mul.mp hdiv) with h5a | hpaq
  · rcases (Nat.prime.dvd_mul.mp h5) with h5a' | h5pq
    · left; exact ⟨by simpa [h5a'] using rfl, by
        have : a = 1 := by
          have : a ∣ 5 := h5a
          exact (Nat.prime.dvd_of_dvd_mul_left hp).mp this
        simpa [this]⟩
    · rcases (Nat.prime.dvd_mul.mp hp) with hpa | hpq
      · have : a = 5 := by
          have : a ∣ 5 := h5a
          exact (Nat.prime.dvd_of_dvd_mul_left h5).mp this
        right; left; exact ⟨this, by
          have : b = p * q := by
            have : a * b = 5 * p * q := hprod
            simpa [this] using congrArg (fun t => t / a) (Nat.mul_div_cancel' (by
              have : a ∣ 5 * p * q := ⟨b, hprod.symm⟩
              exact this))
          exact this⟩
      · have : a = 5 * p := by
          have : a ∣ 5 * p := by
            have : a ∣ 5 * p * q := ⟨b, hprod.symm⟩
            exact Nat.dvd_of_dvd_mul_left this
          exact (Nat.prime.dvd_mul.mp h5).resolve_left (by
            have : ¬ a ∣ 5 := by
              intro h
              have : a ≤ 5 := Nat.le_of_dvd (Nat.succ_pos _) h
              have : a = 1 ∨ a = 5 := Nat.eq_one_of_dvd_one (Nat.dvd_trans h (Nat.dvd_refl 5))
              cases this <;> simp_all)
        right; right; left; exact ⟨this, by
          have : b = q := by
            have : a * b = 5 * p * q := hprod
            simpa [this] using congrArg (fun t => t / a) (Nat.mul_div_cancel' (by
              have : a ∣ 5 * p * q := ⟨b, hprod.symm⟩
              exact this))
          exact this⟩
  · rcases (Nat.prime.dvd_mul.mp hp) with hpa | hpq
    · have : a = p := by
        have : a ∣ p := by
          have : a ∣ 5 * p * q := ⟨b, hprod.symm⟩
          exact Nat.dvd_of_dvd_mul_left this
        exact (Nat.prime.dvd_of_dvd_mul_left hp).mp this
      right; right; right; left; exact ⟨this, by
        have : b = 5 * q := by
          have : a * b = 5 * p * q := hprod
          simpa [this] using congrArg (fun t => t / a) (Nat.mul_div_cancel' (by
            have : a ∣ 5 * p * q := ⟨b, hprod.symm⟩
            exact this))
        exact this⟩
    · have : a = q := by
        have : a ∣ q := by
          have : a ∣ 5 * p * q := ⟨b, hprod.symm⟩
          exact Nat.dvd_of_dvd_mul_left this
        exact (Nat.prime.dvd_of_dvd_mul_left hq).mp this
      right; right; right; right; exact ⟨this, by
        have : b = 5 * p := by
          have : a * b = 5 * p * q := hprod
          simpa [this] using congrArg (fun t => t / a) (Nat.mul_div_cancel' (by
            have : a ∣ 5 * p * q := ⟨b, hprod.symm⟩
            exact this))
        exact this⟩

/-- Main theorem. -/
theorem rmo_2001_2 (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
  (∃ m : ℕ, p ^ 2 + 7 * p * q + q ^ 2 = m ^ 2) ↔
    (p = q ∨ (p = 3 ∧ q = 11) ∨ (p = 11 ∧ q = 3)) := by
  constructor
  · intro h
    rcases h with ⟨m, hm⟩
    have hpos : p + q ≤ m := by
      have : (p + q) ^ 2 ≤ p ^ 2 + 7 * p * q + q ^ 2 := by
        have : 5 * p * q ≤ 7 * p * q := by
          have : (5 : ℕ) ≤ 7 := by decide
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ this)
        simpa [pow_two, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
          mul_assoc, add_mul, mul_add, two_mul] using
          Nat.add_le_add (Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) this))
            (Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) this))
      have : (p + q) ^ 2 ≤ m ^ 2 := by simpa [hm] using this
      exact Nat.le_of_pow_le_pow (Nat.succ_pos _) this
    set a := m - (p + q) with ha
    set b := m + (p + q) with hb
    have hmul : a * b = 5 * p * q := by
      have : (m - (p + q)) * (m + (p + q)) = m ^ 2 - (p + q) ^ 2 := by
        ring
      have : (m - (p + q)) * (m + (p + q)) = 5 * p * q := by
        have : m ^ 2 - (p + q) ^ 2 = 5 * p * q := by
          have : p ^ 2 + 7 * p * q + q ^ 2 = m ^ 2 := hm
          have : (p + q) ^ 2 + 5 * p * q = m ^ 2 := by
            simpa [pow_two, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
              mul_assoc, add_mul, mul_add, two_mul] using this
          have : m ^ 2 - (p + q) ^ 2 = 5 * p * q := by
            have := Nat.sub_eq_iff_eq_add (Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) this))
            simpa [this] using congrArg (fun t => t - (p + q) ^ 2) this
          exact this
        simpa [ha, hb] using this
      simpa [ha, hb] using this
    have hdiff : b - a = 2 * (p + q) := by
      have : b - a = (m + (p + q)) - (m - (p + q)) := by
        simp [ha, hb]
      simpa [two_mul, add_comm, add_left_comm, add_assoc] using this
    rcases factor_cases p q a b hp hq hmul hdiff with
      (⟨h1, h2⟩ | (⟨h1, h2⟩ | (⟨h1, h2⟩ | (⟨h1, h2⟩ | (⟨h1, h2⟩ | ⟨h1, h2⟩))))))
    · have : p = q := by
        have : a = 1 := by simpa [h1] using rfl
        have : b = 5 * p * q := h2
        have : 5 * p * q - 1 = 2 * (p + q) := by
          have := hdiff
          simpa [ha, hb, h1, h2] using this
        linarith
      exact Or.inl this
    · have : p = 3 ∧ q = 11 := by
        have hp3 : p = 3 := by
          have : a = 5 := h1
          have : b = p * q := h2
          have : 5 * p * q - 5 = 2 * (p + q) := by
            simpa [ha, hb, h1, h2] using hdiff
          linarith
        have hq11 : q = 11 := by
          have : a = 5 := h1
          have : b = p * q := h2
          have : 5 * p * q - 5 = 2 * (p + q) := by
            simpa [ha, hb, h1, h2] using hdiff
          linarith
        exact ⟨hp3, hq11⟩
      exact Or.inr <| Or.inl this
    · have : p = 11 ∧ q = 3 := by
        have hp11 : p = 11 := by
          have : a = p := h1
          have : b = 5 * q := h2
          have : 5 * p * q - p = 2 * (p + q) := by
            simpa [ha, hb, h1, h2] using hdiff
          linarith
        have hq3 : q = 3 := by
          have : a = p := h1
          have : b = 5 * q := h2
          have : 5 * p * q - p = 2 * (p + q) := by
            simpa [ha, hb, h1, h2] using hdiff
          linarith
        exact ⟨hp11, hq3⟩
      exact Or.inr <| Or.inr this
    · have : p = q := by
        have : a = p * q := h1
        have : b = 5 := h2
        have : 5 - p * q = 2 * (p + q) := by
          simpa [ha, hb, h1, h2] using hdiff
        linarith
      exact Or.inl this
    · have : p = q := by
        have : a = 5 * p * q := h1
        have : b = 1 := h2
        have : 1 - 5 * p * q = 2 * (p + q) := by
          simpa [ha, hb, h1, h2] using hdiff
        linarith
      exact Or.inl this
  · intro h
    rcases h with h | h | h
    · rcases h with rfl
      refine ⟨p + 5 * p, ?_⟩
      calc
        p ^ 2 + 7 * p * p + p ^ 2 = (p + p) ^ 2 + 5 * p * p := by
          ring
        _ = (2 * p + 5 * p) ^ 2 := by
          ring
    · rcases h with ⟨hp3, hq11⟩
      subst hp3; subst hq11
      refine ⟨34, ?_⟩
      norm_num
    · rcases h with ⟨hp11, hq3⟩
      subst hp11; subst hq3
      refine ⟨34, ?_⟩
      norm_num
