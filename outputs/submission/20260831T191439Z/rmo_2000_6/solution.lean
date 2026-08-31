import Mathlib.Data.Nat.Basic
import Mathlib.Order.Bounds.Basic

-- Helper lemmas for part 1: a²b⁵ divisible by 2000
lemma min_ab_part1_exists : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ a * b = 10 := by exact ⟨1, 10, by decide, by decide, by norm_num, by rfl⟩

lemma min_ab_part1_lower_bound : ∀ a b : ℕ, 0 < a → 0 < b → 2000 ∣ a ^ 2 * b ^ 5 → a * b ≥ 10 := by sorry

-- Helper lemmas for part 2: a³b⁴ divisible by 2000  
lemma min_ab_part2_exists : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ a * b = 10 := by exact
  ⟨5, 2,
    ⟨by decide,
      ⟨by decide,
        ⟨by
          refine ⟨1, ?_⟩
          norm_num,
         by decide⟩⟩⟩⟩

lemma min_ab_part2_lower_bound : ∀ a b : ℕ, 0 < a → 0 < b → 2000 ∣ a ^ 3 * b ^ 4 → a * b ≥ 10 := by sorry

-- Auxiliary: factorization of 2000
lemma two_thousand_factorization : 2000 = 2 ^ 4 * 5 ^ 3 := by linarith

-- Main theorem combining both parts
theorem rmo_2000_6 :
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} 10) ∧
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} 10) := by sorry
