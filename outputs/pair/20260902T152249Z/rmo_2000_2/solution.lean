import Mathlib

theorem rmo_2000_2
  (x y : ℕ)
  (hx : 0 < x)
  (hy : 0 < y)
  (h : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8) :
  x = 9 ∧ y = 11 := by
  have h₁ : x ≥ 9 := by
    by_contra! hx'
    have h₂ : x ≤ 8 := by linarith
    have h₃ : y ≤ x + 1 := by
      have h₄ : (x + 2) ^ 3 > x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := by
        have h₅ : x ≤ 8 := h₂
        interval_cases x <;> norm_num at h ⊢ <;> nlinarith
      have h₆ : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := h
      have h₇ : y ^ 3 < (x + 2) ^ 3 := by
        rw [h₆]
        exact h₄
      have h₈ : y < x + 2 := by
        intro h₉
        have h₁₀ : y ≥ x + 2 := h₉
        have h₁₁ : y ^ 3 ≥ (x + 2) ^ 3 := by
          exact Nat.pow_le_pow_of_le_left h₁₀ 3
        linarith
      omega
    have h₉ : y ^ 3 ≤ (x + 1) ^ 3 := by
      exact Nat.pow_le_pow_of_le_left h₃ 3
    have h₁₀ : (x + 1) ^ 3 < x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := by
      have h₁₁ : x ≤ 8 := h₂
      interval_cases x <;> norm_num at h ⊢ <;> nlinarith
    have h₁₁ : y ^ 3 < x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := by
      calc
        y ^ 3 ≤ (x + 1) ^ 3 := h₉
        _ < x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := h₁₀
    linarith
  
  have h₂ : y ≤ x + 3 := by
    have h₃ : x ^ 3 + 8 * x ^ 2 - 6 * x + 8 < (x + 4) ^ 3 := by
      have h₄ : x ≥ 9 := h₁
      have h₅ : (x + 4) ^ 3 = x ^ 3 + 12 * x ^ 2 + 48 * x + 64 := by
        ring_nf
      have h₆ : x ^ 3 + 8 * x ^ 2 - 6 * x + 8 < x ^ 3 + 12 * x ^ 2 + 48 * x + 64 := by
        have h₇ : 0 < x := hx
        have h₈ : 0 < x ^ 2 := by positivity
        have h₉ : 0 < x ^ 3 := by positivity
        omega
      linarith
    have h₄ : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := h
    have h₅ : y ^ 3 < (x + 4) ^ 3 := by
      rw [h₄]
      exact h₃
    have h₆ : y < x + 4 := by
      intro h₇
      have h₈ : y ≥ x + 4 := h₇
      have h₉ : y ^ 3 ≥ (x + 4) ^ 3 := by
        exact Nat.pow_le_pow_of_le_left h₈ 3
      linarith
    omega
  
  have h₃ : y ≥ x + 2 := by
    have h₄ : (x + 1) ^ 3 < x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := by
      have h₅ : x ≥ 9 := h₁
      have h₆ : (x + 1) ^ 3 = x ^ 3 + 3 * x ^ 2 + 3 * x + 1 := by
        ring_nf
      have h₇ : x ^ 3 + 3 * x ^ 2 + 3 * x + 1 < x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := by
        have h₈ : 0 < x := hx
        have h₉ : 0 < x ^ 2 := by positivity
        have h₁₀ : 0 < x ^ 3 := by positivity
        omega
      linarith
    have h₅ : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := h
    have h₆ : (x + 1) ^ 3 < y ^ 3 := by
      rw [h₅]
      exact h₄
    have h₇ : x + 1 < y := by
      intro h₈
      have h₉ : y ≤ x + 1 := h₈
      have h₁₀ : y ^ 3 ≤ (x + 1) ^ 3 := by
        exact Nat.pow_le_pow_of_le_left h₉ 3
      linarith
    omega
  
  have h₄ : y = x + 2 ∨ y = x + 3 := by
    have h₅ : y ≥ x + 2 := h₃
    have h₆ : y ≤ x + 3 := h₂
    omega
  
  cases h₄ with
  | inl h₄ =>
    have h₅ : y = x + 2 := h₄
    have h₆ : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := h
    rw [h₅] at h₆
    have h₇ : (x + 2) ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := by
      exact h₆
    have h₈ : x = 9 := by
      have h₉ : (x + 2) ^ 3 = x ^ 3 + 6 * x ^ 2 + 12 * x + 8 := by
        ring_nf
      rw [h₉] at h₇
      have h₁₀ : x ^ 3 + 6 * x ^ 2 + 12 * x + 8 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := by
        exact h₇
      have h₁₁ : 6 * x ^ 2 + 12 * x = 8 * x ^ 2 - 6 * x := by
        omega
      have h₁₂ : 0 < x := hx
      have h₁₃ : 2 * x ^ 2 - 18 * x = 0 := by
        omega
      have h₁₄ : x * (2 * x - 18) = 0 := by
        ring_nf at h₁₃
        omega
      have h₁₅ : 2 * x - 18 = 0 := by
        have h₁₆ : x ≠ 0 := by linarith
        have h₁₇ : 2 * x - 18 = 0 := by
          apply mul_left_cancel₀ h₁₆
          omega
        exact h₁₇
      omega
    have h₉ : y = 11 := by
      rw [h₈] at h₅
      omega
    exact ⟨h₈, h₉⟩
  | inr h₄ =>
    have h₅ : y = x + 3 := h₄
    have h₆ : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := h
    rw [h₅] at h₆
    have h₇ : (x + 3) ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := by
      exact h₆
    have h₈ : False := by
      have h₉ : (x + 3) ^ 3 = x ^ 3 + 9 * x ^ 2 + 27 * x + 27 := by
        ring_nf
      rw [h₉] at h₇
      have h₁₀ : x ^ 3 + 9 * x ^ 2 + 27 * x + 27 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := by
        exact h₇
      have h₁₁ : 9 * x ^ 2 + 27 * x + 27 = 8 * x ^ 2 - 6 * x + 8 := by
        omega
      have h₁₂ : x ^ 2 + 33 * x + 19 = 0 := by
        omega
      have h₁₃ : 0 < x := hx
      have h₁₄ : x ^ 2 + 33 * x + 19 > 0 := by
        nlinarith
      linarith
    exfalso
    exact h₈
