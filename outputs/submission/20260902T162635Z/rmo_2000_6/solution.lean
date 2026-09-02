import Mathlib.Data.Nat.Basic
import Mathlib.Order.Bounds.Basic

-- Helper lemmas for the RMO 2000 Problem 6

lemma exists_solution_ab_eq_10_part1 :
  ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ a * b = 10 := by sorry

lemma exists_solution_ab_eq_10_part2 :
  ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ a * b = 10 := by sorry

lemma no_solution_ab_lt_10_part1 :
  ∀ n : ℕ, n < 10 → ¬(∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ a * b = n) := by sorry

lemma no_solution_ab_lt_10_part2 :
  ∀ n : ℕ, n < 10 → ¬(∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ a * b = n) := by sorry

-- Prime factorization facts about 2000
lemma two_thousand_factorization :
  2000 = 2 ^ 4 * 5 ^ 3 := by linarith

lemma div_by_two_thousand_iff :
  ∀ x : ℕ, 2000 ∣ x ↔ (2 ^ 4 ∣ x ∧ 5 ^ 3 ∣ x) := by omega

lemma product_of_positive_is_positive :
  ∀ a b : ℕ, 0 < a → 0 < b → 0 < a * b := by simp_all

lemma ab_le_n_implies_a_le_n :
  ∀ a b n : ℕ, 0 < a → 0 < b → a * b = n → a ≤ n := by aesop

lemma ab_le_n_implies_b_le_n :
  ∀ a b n : ℕ, 0 < a → 0 < b → a * b = n → b ≤ n := by aesop

lemma omega_check_for_small_values :
  ∀ k : ℕ, k < 10 → k ≠ 0 → k ≠ 1 → k ≠ 2 → k ≠ 3 → k ≠ 4 → 
    k ≠ 5 → k ≠ 6 → k ≠ 7 → k ≠ 8 → k ≠ 9 → False := by omega

theorem rmo_2000_6 :
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} 10) ∧
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} 10) := by
  sorry