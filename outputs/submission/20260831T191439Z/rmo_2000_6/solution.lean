import Mathlib.Data.Nat.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic

theorem rmo_2000_6 :
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} 10) ∧
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} 10) := by
  constructor
  · -- First part: IsLeast for set where 2000 ∣ a²b⁵
    constructor
    · -- Show 10 is in the set (take a=1, b=10)
      refine' ⟨1, 10, by decide, by decide, _, rfl⟩
      · norm_num
    · -- Show any element is ≥ 10
      intro n hn
      rcases hn with ⟨a, b, ha, hb, hdiv, heq⟩
      subst heq
      by_contra h
      have : a * b < 10 := by omega
      have : a ≤ 9 := by nlinarith
      have : b ≤ 9 := by nlinarith
      interval_cases a <;> interval_cases b <;>
        (try omega) <;>
        (try { norm_num at hdiv ⊢; omega })
  · -- Second part: IsLeast for set where 2000 ∣ a³b⁴
    constructor
    · -- Show 10 is in the set (take a=1, b=10)
      refine' ⟨1, 10, by decide, by decide, _, rfl⟩
      · norm_num
    · -- Show any element is ≥ 10
      intro n hn
      rcases hn with ⟨a, b, ha, hb, hdiv, heq⟩
      subst heq
      by_contra h
      have : a * b < 10 := by omega
      have : a ≤ 9 := by nlinarith
      have : b ≤ 9 := by nlinarith
      interval_cases a <;> interval_cases b <;>
        (try omega) <;>
        (try { norm_num at hdiv ⊢; omega })
