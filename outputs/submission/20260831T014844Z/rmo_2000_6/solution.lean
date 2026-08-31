import Mathlib.Data.Nat.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic.IntervalCases

theorem rmo_2000_6 :
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} 10) ∧
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} 10) := by
  constructor
  · -- First part: IsLeast for a²b⁵
    constructor
    · -- Show 10 ∈ S₁: use a = 1, b = 10
      use 1, 10
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num [pow_succ]
      rfl
    · -- Show 10 ≤ all elements in S₁
      intro n hn
      rcases hn with ⟨a, b, ha, hb, hdiv, hmn⟩
      rw [hmn]
      by_contra hlt
      have : a * b < 10 := by omega
      have : a ≤ 9 := by
        nlinarith
      have : b ≤ 9 := by
        nlinarith
      interval_cases a <;> interval_cases b <;> simp_all [Nat.pow_succ, Nat.mul_assoc]
      <;> norm_num at * <;> omega
  
  · -- Second part: IsLeast for a³b⁴
    constructor
    · -- Show 10 ∈ S₂: use a = 5, b = 2
      use 5, 2
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num [pow_succ]
      rfl
    · -- Show 10 ≤ all elements in S₂
      intro n hn
      rcases hn with ⟨a, b, ha, hb, hdiv, hmn⟩
      rw [hmn]
      by_contra hlt
      have : a * b < 10 := by omega
      have : a ≤ 9 := by
        nlinarith
      have : b ≤ 9 := by
        nlinarith
      interval_cases a <;> interval_cases b <;> simp_all [Nat.pow_succ, Nat.mul_assoc]
      <;> norm_num at * <;> omega
