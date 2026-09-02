import Mathlib

open Nat

-- Helper: When p = q, the expression is always a perfect square (3p)²
lemma equal_primes_case (p : ℕ) (hp : Nat.Prime p) :
  ∃ m : ℕ, p^2 + 7*p*p + p^2 = m^2 := by
  refine' ⟨3 * p, _⟩
  ring

-- Helper: If p ≠ q and both are at least 3, then solution exists only for (3,11) or (11,3)
lemma large_primes_neq_case (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
  (hneq : p ≠ q) (hge3p : 3 ≤ p) (hge3q : 3 ≤ q) :
  (∃ m : ℕ, p^2 + 7*p*q + q^2 = m^2) ↔
    ((p = 3 ∧ q = 11) ∨ (p = 11 ∧ q = 3)) := by sorry

-- Helper: Handle cases where one prime is less than 3 (i.e., equals 2 since prime)
lemma small_prime_case (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
  (hneq : p ≠ q) (hsmall : p < 3 ∨ q < 3) :
  ¬∃ m : ℕ, p^2 + 7*p*q + q^2 = m^2 := by sorry

-- Helper: Both primes ≥ 3 but not necessarily distinct
lemma both_ge_three_case (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
  (hge3p : 3 ≤ p) (hge3q : 3 ≤ q) :
  (∃ m : ℕ, p^2 + 7*p*q + q^2 = m^2) ↔ (p = q ∨ (p = 3 ∧ q = 11) ∨ (p = 11 ∧ q = 3)) := by sorry

-- Helper: At least one prime < 3 implies neither equals 3 nor 11
lemma less_than_three_implies_no_solution (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
  (hlt3 : p < 3 ∨ q < 3) :
  ¬((p = 3 ∧ q = 11) ∨ (p = 11 ∧ q = 3)) := by omega

-- Main theorem characterizing all solutions
theorem rmo_2001_2 (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
  (∃ m : ℕ, p^2 + 7*p*q + q^2 = m^2) ↔
    (p = q ∨ (p = 3 ∧ q = 11) ∨ (p = 11 ∧ q = 3)) := by -- Candidate 1: Direct case analysis with helper lemma applications
    cases' eq_or_ne p q with h_eq h_neq
    · -- Case p = q
      have : ∃ m : ℕ, p^2 + 7*p*q + q^2 = m^2 := by
        refine' ⟨3 * p, _⟩
        rw [h_eq]
        ring
      have : p = q ∨ (p = 3 ∧ q = 11) ∨ (p = 11 ∧ q = 3) := Or.inl h_eq
      constructor <;> simp_all [h_eq] <;> aesop
    · -- Case p ≠ q
      by_cases h_both_ge3 : 3 ≤ p ∧ 3 ≤ q
      · -- Both primes ≥ 3
        rcases h_both_ge3 with ⟨h_pge3, h_qge3⟩
        have := both_ge_three_case p q hp hq h_pge3 h_qge3
        simp_all [h_neq]
        <;> aesop
      · -- At least one prime < 3
        have h_small : p < 3 ∨ q < 3 := by
          by_contra! h
          exact h_both_ge3 ⟨h.1, h.2⟩
        have := small_prime_case p q hp hq h_neq h_small
        simp_all [h_neq]
        <;> aesop
