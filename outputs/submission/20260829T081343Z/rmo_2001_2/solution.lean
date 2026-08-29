import Mathlib

open Nat

-- Helper: Backward direction case 1 - p equals q
lemma backward_p_eq_q (p q : ℕ) (h_eq : p = q) :
  ∃ m : ℕ, p^2 + 7*p*q + q^2 = m^2 := by
  subst h_eq
  use 3 * p
  ring

-- Helper: Backward direction case 2 - p = 3, q = 11
lemma backward_p_3_q_11 :
  ∃ m : ℕ, 3^2 + 7*3*11 + 11^2 = m^2 := by
  use 19
  norm_num

-- Helper: Backward direction case 3 - p = 11, q = 3
lemma backward_p_11_q_3 :
  ∃ m : ℕ, 11^2 + 7*11*3 + 3^2 = m^2 := by
  use 19
  norm_num

-- Helper: Expression difference analysis
lemma expression_difference_from_square (p q : ℕ) :
  p^2 + 7*p*q + q^2 - (p + q)^2 = 5*p*q := by
  ring_nf
  <;> omega

-- Helper: Forward direction when p ≠ q (core number theory)
lemma forward_distinct_primes (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (h_neq : p ≠ q) 
    (h_exists : ∃ m : ℕ, p^2 + 7*p*q + q^2 = m^2) :
  (p = 3 ∧ q = 11) ∨ (p = 11 ∧ q = 3) := by sorry

-- Main backward implication
theorem backward_direction (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
  (p = q ∨ (p = 3 ∧ q = 11) ∨ (p = 11 ∧ q = 3)) → (∃ m : ℕ, p^2 + 7*p*q + q^2 = m^2) := by
  intro h_or
  cases h_or with
  | inl h_eq =>
    exact backward_p_eq_q p q h_eq
  | inr h_pair =>
    cases h_pair with
    | inl h3 =>
      have h3p : p = 3 := h3.1
      have h11q : q = 11 := h3.2
      rw [h3p, h11q]
      exact backward_p_3_q_11
    | inr h11 =>
      have h11p : p = 11 := h11.1
      have h3q : q = 3 := h11.2
      rw [h11p, h3q]
      exact backward_p_11_q_3

-- Helper: Analysis of the forward direction when p ≠ q
theorem forward_direction (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
  (∃ m : ℕ, p^2 + 7*p*q + q^2 = m^2) → (p = q ∨ (p = 3 ∧ q = 11) ∨ (p = 11 ∧ q = 3)) := by
  intro h_exists
  by_cases h_eq : p = q
  · exact Or.inl h_eq
  · have h_neq : p ≠ q := h_eq
    have h_specific : (p = 3 ∧ q = 11) ∨ (p = 11 ∧ q = 3) := 
      forward_distinct_primes p q hp hq h_neq h_exists
    cases h_specific with
    | inl h3 =>
      exact Or.inr (Or.inl h3)
    | inr h11 =>
      exact Or.inr (Or.inr h11)

-- Main theorem statement (kept identical to challenge)
theorem rmo_2001_2 (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
  (∃ m : ℕ, p^2 + 7*p*q + q^2 = m^2) ↔
    (p = q ∨ (p = 3 ∧ q = 11) ∨ (p = 11 ∧ q = 3)) := by exact ⟨forward_direction p q hp hq, backward_direction p q hp hq⟩
