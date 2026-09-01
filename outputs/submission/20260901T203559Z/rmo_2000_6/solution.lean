import Mathlib.Data.Nat.Basic
import Mathlib.Order.Bounds.Basic

theorem rmo_2000_6 :
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} 10) ∧
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} 10) := by
  constructor
  
  · -- First IsLeast: min value is 10 for a²b⁵ divisible by 2000
    constructor
    
    · -- Show 10 is in the set
      refine' ⟨1, 10, by decide, by decide, _ , rfl⟩
      norm_num
      
    · -- Show 10 is minimal
      intro n hn
      rcases hn with ⟨a, b, ha, hb, hdiv, hn_eq⟩
      subst hn_eq
      have h₁ : 2000 ∣ a ^ 2 * b ^ 5 := hdiv
      have h₂ : 0 < a := ha
      have h₃ : 0 < b := hb
      
      by_contra h
      have h₄ : a * b < 10 := by linarith
      
      -- Case analysis since ab < 10
      have h₅ : a ≤ 9 := by
        nlinarith
      have h₆ : b ≤ 9 := by
        nlinarith
      
      interval_cases a <;> interval_cases b <;> 
        simp_all (config := {decide := true})
        
  · -- Second IsLeast: min value is 10 for a³b⁴ divisible by 2000
    constructor
    
    · -- Show 10 is in the set
      refine' ⟨5, 2, by decide, by decide, _ , rfl⟩
      norm_num
      
    · -- Show 10 is minimal
      intro n hn
      rcases hn with ⟨a, b, ha, hb, hdiv, hn_eq⟩
      subst hn_eq
      have h₁ : 2000 ∣ a ^ 3 * b ^ 4 := hdiv
      have h₂ : 0 < a := ha
      have h₃ : 0 < b := hb
      
      by_contra h
      have h₄ : a * b < 10 := by linarith
      
      -- Case analysis since ab < 10
      have h₅ : a ≤ 9 := by
        nlinarith
      have h₆ : b ≤ 9 := by
        nlinarith
      
      interval_cases a <;> interval_cases b <;> 
        simp_all (config := {decide := true})