import Mathlib

open Nat

theorem rmo_2001_2 (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
  (∃ m : ℕ, p^2 + 7*p*q + q^2 = m^2) ↔
    (p = q ∨ (p = 3 ∧ q = 11) ∨ (p = 11 ∧ q = 3)) := by
  constructor
  · -- Forward direction: if p² + 7pq + q² is a square, then p = q or (p,q) = (3,11) or (11,3)
    intro h
    rcases h with ⟨m, hm⟩
    have h₁ : p ≤ m := by
      nlinarith [Nat.Prime.two_le hp, Nat.Prime.two_le hq]
    have h₂ : q ≤ m := by
      nlinarith [Nat.Prime.two_le hp, Nat.Prime.two_le hq]
    
    -- Case analysis based on whether p = q
    by_cases h_eq : p = q
    · exact Or.inl h_eq
    · -- p ≠ q case
      have h_neq : p ≠ q := h_eq
      -- We'll use the fact that p² + 7pq + q² = m² implies certain divisibility properties
      have h_main : (p = 3 ∧ q = 11) ∨ (p = 11 ∧ q = 3) := by
        -- Key insight: complete the square and analyze the resulting equation
        have h₃ : p^2 + 7*p*q + q^2 = m^2 := hm
        have h₄ : (p + q)^2 + 5*p*q = m^2 := by
          ring_nf at h₃ ⊢
          linarith
        have h₅ : m^2 - (p + q)^2 = 5*p*q := by
          linarith
        have h₆ : (m - (p + q)) * (m + (p + q)) = 5*p*q := by
          have h₇ : m ≥ p + q := by
            nlinarith [Nat.Prime.two_le hp, Nat.Prime.two_le hq]
          have h₈ : m^2 - (p + q)^2 = (m - (p + q)) * (m + (p + q)) := by
            rw [← Nat.mul_sub_left_distrib, ← Nat.mul_sub_right_distrib]
            ring_nf
            <;> omega
          rw [h₈] at h₅
          exact h₅
        -- Analyze the factorization of 5*p*q
        have h₇ : m - (p + q) > 0 := by
          by_contra h₈
          have h₉ : m - (p + q) = 0 := by omega
          have h₁₀ : m = p + q := by omega
          rw [h₁₀] at h₃
          have h₁₁ : p^2 + 7*p*q + q^2 = (p + q)^2 := by
            simp [pow_two] at h₃ ⊢
            <;> ring_nf at h₃ ⊢ <;> omega
          have h₁₂ : 5*p*q = 0 := by
            nlinarith
          have h₁₃ : p = 0 ∨ q = 0 := by
            apply eq_zero_or_eq_zero_of_mul_eq_zero h₁₂
          cases' h₁₃ with h₁₄ h₁₄
          · exfalso
            exact Nat.Prime.ne_zero hp h₁₄
          · exfalso
            exact Nat.Prime.ne_zero hq h₁₄
        have h₈ : m + (p + q) > 0 := by
          nlinarith [Nat.Prime.two_le hp, Nat.Prime.two_le hq]
        
        -- Since 5*p*q has limited factorizations, we check each possibility
        have h₉ : p = 3 ∨ p = 11 := by
          -- Through careful analysis of the factor pairs of 5*p*q
          have h₁₀ : p ≤ 11 := by
            by_contra h₁₁
            have h₁₂ : p ≥ 13 := by omega
            have h₁₃ : q ≥ 2 := Nat.Prime.two_le hq
            have h₁₄ : p^2 + 7*p*q + q^2 < (p + 4*q)^2 := by
              nlinarith
            have h₁₅ : (p + 3*q)^2 < p^2 + 7*p*q + q^2 := by
              nlinarith
            have h₁₆ : ¬∃ m : ℕ, p^2 + 7*p*q + q^2 = m^2 := by
              intro h₁₇
              rcases h₁₇ with ⟨m, h₁₈⟩
              have h₁₉ : p + 3*q < m := by
                nlinarith
              have h₂₀ : m < p + 4*q := by
                nlinarith
              omega
            exact h₁₆ h
          interval_cases p <;> norm_num at hp ⊢ <;> 
            (try contradiction) <;>
            (try {
              have h₁₁ : q ≤ 11 := by
                by_contra h₁₂
                have h₁₃ : q ≥ 13 := by omega
                have h₁₄ : p^2 + 7*p*q + q^2 < (p + 4*q)^2 := by
                  nlinarith
                have h₁₅ : (p + 3*q)^2 < p^2 + 7*p*q + q^2 := by
                  nlinarith
                have h₁₆ : ¬∃ m : ℕ, p^2 + 7*p*q + q^2 = m^2 := by
                  intro h₁₇
                  rcases h₁₇ with ⟨m, h₁₈⟩
                  have h₁₉ : p + 3*q < m := by
                    nlinarith
                  have h₂₀ : m < p + 4*q := by
                    nlinarith
                  omega
                exact h₁₆ h
              interval_cases q <;> norm_num at hq ⊢ <;>
                (try contradiction) <;>
                (try {
                  have h₁₁ : ∃ m : ℕ, p^2 + 7*p*q + q^2 = m^2 := by
                    use 14
                    norm_num
                  contradiction
                })
            }) <;>
            (try {
              have h₁₁ : q ≤ 11 := by
                by_contra h₁₂
                have h₁₃ : q ≥ 13 := by omega
                have h₁₄ : p^2 + 7*p*q + q^2 < (p + 4*q)^2 := by
                  nlinarith
                have h₁₅ : (p + 3*q)^2 < p^2 + 7*p*q + q^2 := by
                  nlinarith
                have h₁₆ : ¬∃ m : ℕ, p^2 + 7*p*q + q^2 = m^2 := by
                  intro h₁₇
                  rcases h₁₇ with ⟨m, h₁₈⟩
                  have h₁₉ : p + 3*q < m := by
                    nlinarith
                  have h₂₀ : m < p + 4*q := by
                    nlinarith
                  omega
                exact h₁₆ h
              interval_cases q <;> norm_num at hq ⊢ <;>
                (try contradiction) <;>
                (try {
                  have h₁₁ : ∃ m : ℕ, p^2 + 7*p*q + q^2 = m^2 := by
                    use 14
                    norm_num
                  contradiction
                })
            })
        cases' h₉ with h₁₀ h₁₀
        · -- p = 3
          have h₁₁ : q = 11 := by
            by_contra h₁₂
            have h₁₃ : q ≠ 11 := h₁₂
            have h₁₄ : q ≤ 11 := by
              by_contra h₁₅
              have h₁₆ : q ≥ 13 := by omega
              have h₁₇ : 3^2 + 7*3*q + q^2 < (3 + 4*q)^2 := by
                nlinarith
              have h₁₈ : (3 + 3*q)^2 < 3^2 + 7*3*q + q^2 := by
                nlinarith
              have h₁₉ : ¬∃ m : ℕ, 3^2 + 7*3*q + q^2 = m^2 := by
                intro h₂₀
                rcases h₂₀ with ⟨m, h₂₁⟩
                have h₂₂ : 3 + 3*q < m := by
                  nlinarith
                have h₂₃ : m < 3 + 4*q := by
                  nlinarith
                omega
              exact h₁₉ h
            interval_cases q <;> norm_num at hq ⊢ <;>
              (try contradiction) <;>
              (try {
                have h₁₅ : ∃ m : ℕ, 3^2 + 7*3*q + q^2 = m^2 := by
                  use 14
                  norm_num
                contradiction
              })
          exact Or.inr ⟨Or.inl rfl, h₁₁⟩
        · -- p = 11
          have h₁₁ : q = 3 := by
            by_contra h₁₂
            have h₁₃ : q ≠ 3 := h₁₂
            have h₁₄ : q ≤ 11 := by
              by_contra h₁₅
              have h₁₆ : q ≥ 13 := by omega
              have h₁₇ : 11^2 + 7*11*q + q^2 < (11 + 4*q)^2 := by
                nlinarith
              have h₁₈ : (11 + 3*q)^2 < 11^2 + 7*11*q + q^2 := by
                nlinarith
              have h₁₉ : ¬∃ m : ℕ, 11^2 + 7*11*q + q^2 = m^2 := by
                intro h₂₀
                rcases h₂₀ with ⟨m, h₂₁⟩
                have h₂₂ : 11 + 3*q < m := by
                  nlinarith
                have h₂₃ : m < 11 + 4*q := by
                  nlinarith
                omega
              exact h₁₉ h
            interval_cases q <;> norm_num at hq ⊢ <;>
              (try contradiction) <;>
              (try {
                have h₁₅ : ∃ m : ℕ, 11^2 + 7*11*q + q^2 = m^2 := by
                  use 14
                  norm_num
                contradiction
              })
          exact Or.inr ⟨Or.inr ⟨rfl, h₁₁⟩⟩
      exact Or.inr h_main
  · -- Reverse direction: if p = q or (p,q) = (3,11) or (11,3), then p² + 7pq + q² is a square
    intro h
    rcases h with (h | h | h)
    · -- Case p = q
      use 3 * p
      rw [h]
      ring_nf
      <;> simp [pow_two]
      <;> ring_nf
    · -- Case p = 3, q = 11
      use 14
      norm_num [h]
    · -- Case p = 11, q = 3
      use 14
      norm_num [h]
