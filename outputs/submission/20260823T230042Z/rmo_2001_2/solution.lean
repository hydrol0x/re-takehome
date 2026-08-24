import Mathlib

open Nat

-- When p = q, p² + 7pq + q² = 9p² = (3p)²
lemma square_when_equal (p : ℕ) :
  p^2 + 7*p*p + p^2 = (3*p)^2 := by linarith

-- If p and q are both prime and equal, then p² + 7pq + q² is a square
lemma exists_square_eq_pq (p : ℕ) (hp : Nat.Prime p) :
  ∃ m : ℕ, p^2 + 7*p*p + p^2 = m^2 := by sorry

-- Case where p=3 and q=11 gives a square
lemma square_case_3_11 :
  3^2 + 7*3*11 + 11^2 = 169 := by sorry

lemma square_case_3_11_is_sq :
  ∃ m : ℕ, 3^2 + 7*3*11 + 11^2 = m^2 := by sorry

-- Case where p=11 and q=3 gives a square
lemma square_case_11_3 :
  11^2 + 7*11*3 + 3^2 = 169 := by sorry

lemma square_case_11_3_is_sq :
  ∃ m : ℕ, 11^2 + 7*11*3 + 3^2 = m^2 := by sorry

-- Forward direction: if there exists m such that p² + 7pq + q² = m², then p=q or (p=3,q=11) or (p=11,q=3)
theorem rmo_2001_2 (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
  (∃ m : ℕ, p^2 + 7*p*q + q^2 = m^2) ↔
    (p = q ∨ (p = 3 ∧ q = 11) ∨ (p = 11 ∧ q = 3)) := by
  sorry
