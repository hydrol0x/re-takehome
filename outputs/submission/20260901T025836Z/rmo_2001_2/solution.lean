import Mathlib

open Nat

lemma eq_self_is_square (p : ℕ) (hp : Nat.Prime p) :
    ∃ m : ℕ, p^2 + 7*p*p + p^2 = m^2 := by
  use 3 * p
  ring

lemma case_3_11 : ∃ m : ℕ, 3^2 + 7*3*11 + 11^2 = m^2 := by
  use 19
  norm_num

lemma case_11_3 : ∃ m : ℕ, 11^2 + 7*11*3 + 3^2 = m^2 := by
  use 19
  norm_num

-- Forward direction: if the expression is a square, then the primes are either equal
-- or the unordered pair {3,11}.
lemma forward_of_existence (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
    (∃ m : ℕ, p^2 + 7*p*q + q^2 = m^2) →
      (p = q ∨ (p = 3 ∧ q = 11) ∨ (p = 11 ∧ q = 3)) := by
  sorry

-- Backward direction: the listed possibilities indeed give a square.
lemma backward_of_condition (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
    (p = q ∨ (p = 3 ∧ q = 11) ∨ (p = 11 ∧ q = 3)) →
      ∃ m : ℕ, p^2 + 7*p*q + q^2 = m^2 := by
  intro h
  rcases h with h | h | h
  · rcases h with rfl
    exact eq_self_is_square _ hp
  · rcases h with ⟨hp3, hq11⟩
    subst hp3
    subst hq11
    exact case_3_11
  · rcases h with ⟨hp11, hq3⟩
    subst hp11
    subst hq3
    exact case_11_3

theorem rmo_2001_2 (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
  (∃ m : ℕ, p^2 + 7*p*q + q^2 = m^2) ↔
    (p = q ∨ (p = 3 ∧ q = 11) ∨ (p = 11 ∧ q = 3)) := by
  constructor
  · intro h
    exact forward_of_existence p q hp hq h
  · intro h
    exact backward_of_condition p q hp hq h
