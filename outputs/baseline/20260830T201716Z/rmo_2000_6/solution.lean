import Mathlib.Data.Nat.Basic
import Mathlib.Order.Bounds.Basic

theorem rmo_2000_6 :
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} 10) ∧
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} 20) := by
  constructor
  · -- First part: IsLeast for the first set with 10
    constructor
    · -- Show 10 is in the set
      use 1, 10
      constructor
      · norm_num
      · constructor
        · norm_num
        · constructor
          · norm_num
          · rfl
    · -- Show 10 is minimal
      intro n hn
      rcases hn with ⟨a, b, ha, hb, hdiv, hn⟩
      rw [hn]
      have h : 10 ≤ a * b := by
        by_contra h'
        have h'' : a * b ≤ 9 := by linarith
        have h''' : a ≤ 9 := by nlinarith
        have h'''' : b ≤ 9 := by nlinarith
        interval_cases a <;> interval_cases b <;> norm_num at hdiv ⊢ <;> 
          (try contradiction) <;> (try omega)
      exact h
  · -- Second part: IsLeast for the second set with 20
    constructor
    · -- Show 20 is in the set
      use 2, 10
      constructor
      · norm_num
      · constructor
        · norm_num
        · constructor
          · norm_num
          · rfl
    · -- Show 20 is minimal
      intro n hn
      rcases hn with ⟨a, b, ha, hb, hdiv, hn⟩
      rw [hn]
      have h : 20 ≤ a * b := by
        by_contra h'
        have h'' : a * b ≤ 19 := by linarith
        have h''' : a ≤ 19 := by nlinarith
        have h'''' : b ≤ 19 := by nlinarith
        -- Check all possibilities where ab < 20
        have h₁ : ¬(∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a * b ≤ 19 ∧ 2000 ∣ a ^ 3 * b ^ 4) := by
          intro ⟨a, b, ha, hb, hab, hdiv⟩
          have : a ≤ 19 := by nlinarith
          have : b ≤ 19 := by nlinarith
          interval_cases a <;> interval_cases b <;> norm_num at hdiv ⊢ <;>
            (try contradiction) <;> (try omega)
        exact h₁ ⟨a, b, ha, hb, h', hdiv⟩
      exact h
