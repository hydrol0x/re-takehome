import Mathlib

open Nat

-- Helper lemma: when p = q, the expression is always a perfect square
lemma eq_case_square (p : ℕ) (hp : Nat.Prime p) :
  ∃ m : ℕ, p^2 + 7*p*p + p^2 = m^2 := by exact ⟨3 * p, by
    ring⟩

-- Helper lemma: the expression is strictly less than (p + 4q)^2 for positive p, q
lemma upper_bound (p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
  p^2 + 7*p*q + q^2 < (p + 4*q)^2 := by nlinarith

-- Helper lemma: the expression is at least (p + 3q)^2 for positive p, q  
lemma lower_bound (p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
  (p + 3*q)^2 ≤ p^2 + 7*p*q + q^2 := by sorry

-- Helper lemma: if p ≠ q and p < q, then (p+3q)^2 < p^2 + 7pq + q^2 < (p+4q)^2
lemma strict_bounds_lt (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hne : p ≠ q) (hlt : p < q) :
  (p + 3*q)^2 < p^2 + 7*p*q + q^2 ∧ p^2 + 7*p*q + q^2 < (p + 4*q)^2 := by sorry

-- Helper lemma: checking specific case (3, 11) gives a perfect square
lemma case_3_11 :
  ∃ m : ℕ, 3^2 + 7*3*11 + 11^2 = m^2 := by exact ⟨19, by decide⟩

-- Helper lemma: checking specific case (11, 3) gives a perfect square  
lemma case_11_3 :
  ∃ m : ℕ, 11^2 + 7*11*3 + 3^2 = m^2 := by exact?

-- Helper lemma: if two consecutive integers have same square, they must be equal
lemma consecutive_squares_distinct (n : ℕ) : n^2 ≠ (n + 1)^2 := by norm_num

-- Forward direction: if expression is square, then one of the three conditions holds
theorem rmo_2001_2_forward (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
  (∃ m : ℕ, p^2 + 7*p*q + q^2 = m^2) →
    (p = q ∨ (p = 3 ∧ q = 11) ∨ (p = 11 ∧ q = 3)) := by sorry

-- Backward direction: if one of the three conditions holds, then expression is square
theorem rmo_2001_2_backward (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
  (p = q ∨ (p = 3 ∧ q = 11) ∨ (p = 11 ∧ q = 3)) →
    (∃ m : ℕ, p^2 + 7*p*q + q^2 = m^2) := by sorry

-- Main theorem combining both directions
theorem rmo_2001_2 (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
  (∃ m : ℕ, p^2 + 7*p*q + q^2 = m^2) ↔
    (p = q ∨ (p = 3 ∧ q = 11) ∨ (p = 11 ∧ q = 3)) := by sorry
