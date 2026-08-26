import Mathlib

open Nat

-- When p = q, the expression equals (3p)²
lemma sq_when_equal (p : ℕ) (hp : Nat.Prime p) :
  ∃ m : ℕ, p^2 + 7*p*p + p^2 = m^2 := by
  refine' ⟨3 * p, _⟩
  ring

-- When p ≠ q and p < q, we need to check finitely many cases
lemma distinct_case_small (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) 
    (hne : p ≠ q) (hlt : p < q) :
  (∃ m : ℕ, p^2 + 7*p*q + q^2 = m^2) → (p = 3 ∧ q = 11) := by sorry

-- When p ≠ q and p > q, we need to check finitely many cases  
lemma distinct_case_large (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hne : p ≠ q) (hgt : p > q) :
  (∃ m : ℕ, p^2 + 7*p*q + q^2 = m^2) → (p = 11 ∧ q = 3) := by sorry

-- Helper: if p and q are distinct primes with p < q and the expression is a square,
-- then p ≤ 11
lemma bound_p_lt_q (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hne : p ≠ q) (hlt : p < q) :
  (∃ m : ℕ, p^2 + 7*p*q + q^2 = m^2) → p ≤ 11 := by sorry

-- Helper: if p and q are distinct primes with p > q and the expression is a square,
-- then q ≤ 11
lemma bound_q_lt_p (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hne : p ≠ q) (hgt : p > q) :
  (∃ m : ℕ, p^2 + 7*p*q + q^2 = m^2) → q ≤ 11 := by sorry

-- The main characterization theorem
theorem rmo_2001_2 (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
  (∃ m : ℕ, p^2 + 7*p*q + q^2 = m^2) ↔
    (p = q ∨ (p = 3 ∧ q = 11) ∨ (p = 11 ∧ q = 3)) := by sorry
