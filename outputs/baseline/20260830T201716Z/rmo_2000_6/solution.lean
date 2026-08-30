import Mathlib.Tactic
import Mathlib.Order.Bounds.Basic

theorem rmo_2000_6 :
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} 10) ∧
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} 10) := by
  constructor
  · -- Part 1: IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} 10
    constructor
    · -- Existence: 10 is in the set
      refine' ⟨5, 2, by decide, by decide, _, rfl⟩
      norm_num [pow_succ]
      rw [Nat.dvd_iff_mod_eq_zero]
      norm_num
    · -- Minimality: 10 is less than or equal to any element
      intro n hn hmn
      rcases hn with ⟨a, b, ha, hb, hdiv, rfl⟩
      have h : 10 ≤ a * b := by
        by_contra hlt
        have hlt' : a * b < 10 := by omega
        have ha' : a < 10 := by
          nlinarith [ha]
        have hb' : b < 10 := by
          nlinarith [hb]
        interval_cases a <;> interval_cases b <;> norm_num at hlt' ⊢
        <;> norm_num at hdiv ⊢
        <;> omega
      exact h
  · -- Part 2: IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} 10
    constructor
    · -- Existence: 10 is in the set
      refine' ⟨5, 2, by decide, by decide, _, rfl⟩
      norm_num [pow_succ]
      rw [Nat.dvd_iff_mod_eq_zero]
      norm_num
    · -- Minimality: 10 is less than or equal to any element
      intro n hn hmn
      rcases hn with ⟨a, b, ha, hb, hdiv, rfl⟩
      have h : 10 ≤ a * b := by
        by_contra hlt
        have hlt' : a * b < 10 := by omega
        have ha' : a < 10 := by
          nlinarith [ha]
        have hb' : b < 10 := by
          nlinarith [hb]
        interval_cases a <;> interval_cases b <;> norm_num at hlt' ⊢
        <;> norm_num at hdiv ⊢
        <;> omega
      exact h
