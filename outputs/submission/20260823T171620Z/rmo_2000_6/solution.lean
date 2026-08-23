import Mathlib.Data.Nat.Basic
import Mathlib.Order.Bounds.Basic

-- Prime factorization of 2000 = 2^4 * 5^3
lemma two_pow_four : 2 ^ 4 = 16 := by norm_num
lemma five_pow_three : 5 ^ 3 = 125 := by norm_num
lemma two_thousand_factorization : 2000 = 2 ^ 4 * 5 ^ 3 := by norm_num

-- Helper: If p^k divides n and p is prime, then valuation_p(n) ≥ k
lemma val_prime_le_of_dvd {p n k : ℕ} (hp : Nat.Prime p) (h : p ^ k ∣ n) : 
  (Nat.factorization n) p ≥ k := by sorry

-- Part 1 helpers: analyzing divisibility conditions
lemma min_value_part1_exists : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ a * b = 10 := by exact ⟨1, 10, by decide, by decide, by decide, by decide⟩

lemma min_value_part1_ge_10 : ∀ n : ℕ, (∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b) → 10 ≤ n := by sorry

-- Part 2 helpers: analyzing divisibility conditions  
lemma min_value_part2_exists : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ a * b = 20 := by use 1, 20
<;> norm_num

lemma min_value_part2_ge_20 : ∀ n : ℕ, (∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b) → 20 ≤ n := by sorry

theorem rmo_2000_6 :
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} 10) ∧
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} 20) := by sorry
