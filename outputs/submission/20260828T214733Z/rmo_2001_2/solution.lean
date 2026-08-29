import Mathlib

open Nat

lemma helper_prime_gt_zero (p : ℕ) (hp : Nat.Prime p) : 0 < p := by
  exact?

lemma helper_prime_ge_two (p : ℕ) (hp : Nat.Prime p) : 2 ≤ p := by
  exact?

lemma helper_compare_primes (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
    p ≤ q ∨ q ≤ p := by
  omega

lemma helper_square_lower_bound (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (m : ℕ) 
    (h_eq : p^2 + 7*p*q + q^2 = m^2) :
    m ≥ p + q := by
  nlinarith

lemma helper_square_upper_bound (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (m : ℕ) 
    (h_eq : p^2 + 7*p*q + q^2 = m^2) :
    m ≤ 3 * max p q := by
  have hp_pos : 0 < p := Nat.Prime.pos hp
  have hq_pos : 0 < q := Nat.Prime.pos hq
  cases le_total p q with
  | inl h_pq =>
    have : max p q = q := by simp [h_pq]
    rw [this]
    have : m^2 ≤ (3*q)^2 := by
      nlinarith [h_pq, mul_le_mul_of_nonneg_left h_pq (Nat.zero_le p)]
    nlinarith
  | inr h_qp =>
    have : max p q = p := by simp [h_qp]
    rw [this]
    have : m^2 ≤ (3*p)^2 := by
      nlinarith [h_qp, mul_le_mul_of_nonneg_right h_qp (Nat.zero_le q)]
    nlinarith

lemma helper_discriminant_nonneg (a b c : ℤ) :
    b^2 - 4*a*c ≥ 0 → ∃ k : ℤ, b^2 - 4*a*c = k^2 := by
  sorry

lemma helper_case_p_eq_q (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) (h_eq : p = q) :
    ∃ m : ℕ, p^2 + 7*p*q + q^2 = m^2 := by
  use 3 * p
  rw [h_eq]
  ring

lemma helper_case_p3_q11_square :
    ∃ m : ℕ, 3^2 + 7*3*11 + 11^2 = m^2 := by
  use 19
  norm_num

lemma helper_case_p11_q3_square :
    ∃ m : ℕ, 11^2 + 7*11*3 + 3^2 = m^2 := by
  use 19
  norm_num

lemma helper_no_other_solutions (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) 
    (h_neq : p ≠ q) (h_sol : ∃ m : ℕ, p^2 + 7*p*q + q^2 = m^2) :
    (p = 3 ∧ q = 11) ∨ (p = 11 ∧ q = 3) := by
  obtain ⟨m, hm⟩ := h_sol
  sorry

lemma helper_implication_forward (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) 
    (h_exists : ∃ m : ℕ, p^2 + 7*p*q + q^2 = m^2) :
    p = q ∨ (p = 3 ∧ q = 11) ∨ (p = 11 ∧ q = 3) := by
  by_cases h_pq : p = q
  · left
    exact h_pq
  · right
    have h_neq : p ≠ q := h_pq
    obtain ⟨m, hm⟩ := h_exists
    have h_sol : (p = 3 ∧ q = 11) ∨ (p = 11 ∧ q = 3) := 
      helper_no_other_solutions p q hp hq h_neq ⟨m, hm⟩
    cases h_sol
    · left
      exact ‹_›
    · right
      exact ‹_›

lemma helper_implication_backward (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) 
    (h_disj : p = q ∨ (p = 3 ∧ q = 11) ∨ (p = 11 ∧ q = 3)) :
    ∃ m : ℕ, p^2 + 7*p*q + q^2 = m^2 := by
  cases h_disj with
    | inl h_pq =>
      exact helper_case_p_eq_q p q hp hq h_pq
    | inr h_or =>
      cases h_or with
      | inl h_and =>
        obtain ⟨h1, h2⟩ := h_and
        subst_vars
        exact helper_case_p3_q11_square
      | inr h_and =>
        obtain ⟨h1, h2⟩ := h_and
        subst_vars
        exact helper_case_p11_q3_square

theorem rmo_2001_2 (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
  (∃ m : ℕ, p^2 + 7*p*q + q^2 = m^2) ↔
    (p = q ∨ (p = 3 ∧ q = 11) ∨ (p = 11 ∧ q = 3)) := by
  constructor
  · exact fun h => helper_implication_forward _ _ hp hq h
  · exact fun h => helper_implication_backward _ _ hp hq h
