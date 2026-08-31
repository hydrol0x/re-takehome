import Mathlib.Data.Nat.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.GCD

-- Helper Lemma 1: Existence of solution for Part 1 (matches target form)
lemma exists_sol_part1 : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ 10 = a * b := by refine ⟨1, 10, ?_, ?_, ?_, ?_⟩ <;> norm_num

-- Helper Lemma 2: Existence of solution for Part 2 (matches target form)
lemma exists_sol_part2 : ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ 10 = a * b := by refine ⟨1, 10, by norm_num, by norm_num, by norm_num, by norm_num⟩

-- Helper Lemma 3: 2 divides ab in Part 1 condition
lemma part1_dvd_2 {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (h : 2000 ∣ a ^ 2 * b ^ 5) : 2 ∣ a * b := by sorry

-- Helper Lemma 4: 5 divides ab in Part 1 condition
lemma part1_dvd_5 {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (h : 2000 ∣ a ^ 2 * b ^ 5) : 5 ∣ a * b := by sorry

-- Helper Lemma 5: 2 divides ab in Part 2 condition
lemma part2_dvd_2 {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (h : 2000 ∣ a ^ 3 * b ^ 4) : 2 ∣ a * b := by sorry

-- Helper Lemma 6: 5 divides ab in Part 2 condition
lemma part2_dvd_5 {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (h : 2000 ∣ a ^ 3 * b ^ 4) : 5 ∣ a * b := by sorry

-- Helper Lemma 7: If 2|n and 5|n then 10|n
lemma dvd_10_of_2_and_5 {n : ℕ} (h2 : 2 ∣ n) (h5 : 5 ∣ n) : 10 ∣ n := by omega

theorem rmo_2000_6 :
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} 10) ∧
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} 10) := by
  apply And.intro
  · -- Part 1
    constructor
    · -- 10 ∈ Set
      exact exists_sol_part1
    · -- 10 ≤ n
      intro n hn
      rcases hn with ⟨a, b, ha, hb, hdiv, rfl⟩
      have h2 : 2 ∣ a * b := part1_dvd_2 ha hb hdiv
      have h5 : 5 ∣ a * b := part1_dvd_5 ha hb hdiv
      have h10 : 10 ∣ a * b := dvd_10_of_2_and_5 h2 h5
      have hpos : 0 < a * b := mul_pos ha hb
      exact Nat.le_of_dvd hpos h10
  · -- Part 2
    constructor
    · -- 10 ∈ Set
      exact exists_sol_part2
    · -- 10 ≤ n
      intro n hn
      rcases hn with ⟨a, b, ha, hb, hdiv, rfl⟩
      have h2 : 2 ∣ a * b := part2_dvd_2 ha hb hdiv
      have h5 : 5 ∣ a * b := part2_dvd_5 ha hb hdiv
      have h10 : 10 ∣ a * b := dvd_10_of_2_and_5 h2 h5
      have hpos : 0 < a * b := mul_pos ha hb
      exact Nat.le_of_dvd hpos h10
