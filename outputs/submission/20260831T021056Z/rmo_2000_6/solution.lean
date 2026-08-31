import Mathlib.Data.Nat.Basic
import Mathlib.Order.Bounds.Basic

-- Factorization of 2000
lemma two_pow_four_times_five_pow_three : (2000 : ℕ) = 2^4 * 5^3 := by norm_num

-- Helper for part 1: lower bound on exponents needed for divisibility
lemma pow_two_divides_condition (a b : ℕ) (h : 2000 ∣ a^2 * b^5) :
    ∃ (a2 b2 a5 b5 : ℕ), 
      a = 2^a2 * 5^a5 ∧ 
      b = 2^b2 * 5^b5 ∧
      2 * a2 + 5 * b2 ≥ 4 ∧
      2 * a5 + 5 * b5 ≥ 3 := by sorry

-- Helper for part 1: minimum exponent sum for 2s
lemma min_exponent_sum_2 : 
    (∀ (a2 b2 : ℕ), 2 * a2 + 5 * b2 ≥ 4 → a2 + b2 ≥ 1) ∧
    (∃ (a2 b2 : ℕ), 2 * a2 + 5 * b2 ≥ 4 ∧ a2 + b2 = 1) := by sorry

-- Helper for part 1: minimum exponent sum for 5s  
lemma min_exponent_sum_5 :
    (∀ (a5 b5 : ℕ), 2 * a5 + 5 * b5 ≥ 3 → a5 + b5 ≥ 1) ∧
    (∃ (a5 b5 : ℕ), 2 * a5 + 5 * b5 ≥ 3 ∧ a5 + b5 = 1) := by sorry

-- Helper for part 1: existence of solution achieving ab = 10
lemma exists_solution_part1 : ∃ (a b : ℕ), 0 < a ∧ 0 < b ∧ 2000 ∣ a^2 * b^5 ∧ a * b = 10 := by sorry

-- Helper for part 1: no smaller solution exists
lemma no_smaller_solution_part1 : 
    ∀ (n : ℕ), n < 10 → ¬(∃ (a b : ℕ), 0 < a ∧ 0 < b ∧ 2000 ∣ a^2 * b^5 ∧ a * b = n) := by sorry

-- Helper for part 2: lower bound on exponents needed for divisibility
lemma pow_three_divides_condition (a b : ℕ) (h : 2000 ∣ a^3 * b^4) :
    ∃ (a2 b2 a5 b5 : ℕ), 
      a = 2^a2 * 5^a5 ∧ 
      b = 2^b2 * 5^b5 ∧
      3 * a2 + 4 * b2 ≥ 4 ∧
      3 * a5 + 4 * b5 ≥ 3 := by sorry

-- Helper for part 2: minimum exponent sum for 2s
lemma min_exponent_sum_2_part2 : 
    (∀ (a2 b2 : ℕ), 3 * a2 + 4 * b2 ≥ 4 → a2 + b2 ≥ 1) ∧
    (∃ (a2 b2 : ℕ), 3 * a2 + 4 * b2 ≥ 4 ∧ a2 + b2 = 1) := by sorry

-- Helper for part 2: minimum exponent sum for 5s  
lemma min_exponent_sum_5_part2 :
    (∀ (a5 b5 : ℕ), 3 * a5 + 4 * b5 ≥ 3 → a5 + b5 ≥ 1) ∧
    (∃ (a5 b5 : ℕ), 3 * a5 + 4 * b5 ≥ 3 ∧ a5 + b5 = 1) := by sorry

-- Helper for part 2: existence of solution achieving ab = 10
lemma exists_solution_part2 : ∃ (a b : ℕ), 0 < a ∧ 0 < b ∧ 2000 ∣ a^3 * b^4 ∧ a * b = 10 := by sorry

-- Helper for part 2: no smaller solution exists
lemma no_smaller_solution_part2 : 
    ∀ (n : ℕ), n < 10 → ¬(∃ (a b : ℕ), 0 < a ∧ 0 < b ∧ 2000 ∣ a^3 * b^4 ∧ a * b = n) := by sorry

theorem rmo_2000_6 :
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} 10) ∧
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} 10) := by sorry
