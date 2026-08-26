import Mathlib

open Nat

theorem rmo_2001_2 (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
  (∃ m : ℕ, p^2 + 7*p*q + q^2 = m^2) ↔
    (p = q ∨ (p = 3 ∧ q = 11) ∨ (p = 11 ∧ q = 3)) := by sorry

lemma eq_case_square (p : ℕ) (hp : Nat.Prime p) :
  ∃ m : ℕ, p^2 + 7*p*p + p^2 = m^2 := by exact ⟨3 * p, by ring⟩

lemma case_3_11 :
  ∃ m : ℕ, 3^2 + 7*3*11 + 11^2 = m^2 := by exact ⟨19, by decide⟩

lemma case_11_3 :
  ∃ m : ℕ, 11^2 + 7*11*3 + 3^2 = m^2 := by exact ⟨19, by decide⟩

lemma lower_bound_strict (p q : ℕ) (hp_pos : 0 < p) (hq_pos : 0 < q) :
  (p + q)^2 < p^2 + 7*p*q + q^2 := by nlinarith

lemma upper_bound_comparison (p q : ℕ) (hq_pos : 0 < q) :
  p^2 + 7*p*q + q^2 < (p + 4*q)^2 := by nlinarith

lemma upper_bound_p_lt_q (p q : ℕ) (hp_lt : p < q) (hq_pos : 0 < q) :
  p^2 + 7*p*q + q^2 < (p + 3*q)^2 := by nlinarith

lemma upper_bound_q_lt_p (p q : ℕ) (hq_lt : q < p) (hp_pos : 0 < p) :
  p^2 + 7*p*q + q^2 < (4*p + q)^2 := by nlinarith

lemma prime_gt_zero (p : ℕ) (hp : Nat.Prime p) : 0 < p := by
  have := Nat.Prime.pos hp
  linarith

lemma lemma_eq_direction (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
  (p = q ∨ (p = 3 ∧ q = 11) ∨ (p = 11 ∧ q = 3)) → 
  ∃ m : ℕ, p^2 + 7*p*q + q^2 = m^2 := by exact?

lemma lemma_neq_cases (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
  p ≠ q → ¬(p = 3 ∧ q = 11) → ¬(p = 11 ∧ q = 3) →
  ¬∃ m : ℕ, p^2 + 7*p*q + q^2 = m^2 := by sorry
