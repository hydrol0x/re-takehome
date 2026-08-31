import Mathlib.Data.Nat.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic

theorem rmo_part1 : IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} 10 := by sorry

theorem rmo_part2 : IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} 10 := by sorry

theorem rmo_2000_6 :
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} 10) ∧
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} 10) := by sorry

-- Helper lemmas for part 1
lemma exists_ab_for_part1 : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ a * b = 10 := by refine ⟨1, 10, by norm_num, by norm_num, by norm_num, by norm_num⟩

lemma min_val_part1_ge_10 : ∀ a b : ℕ, 0 < a → 0 < b → 2000 ∣ a ^ 2 * b ^ 5 → 10 ≤ a * b := by sorry

-- Helper lemmas for part 2  
lemma exists_ab_for_part2 : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ a * b = 10 := by sorry

lemma min_val_part2_ge_10 : ∀ a b : ℕ, 0 < a → 0 < b → 2000 ∣ a ^ 3 * b ^ 4 → 10 ≤ a * b := by sorry
