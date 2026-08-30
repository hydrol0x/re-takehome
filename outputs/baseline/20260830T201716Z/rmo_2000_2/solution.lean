import Mathlib

theorem rmo_2000_2
  (x y : ℕ)
  (hx : 0 < x)
  (hy : 0 < y)
  (h : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8) :
  x = 9 ∧ y = 11 := by
  have h₁ : x ≤ 9 ∨ x ≥ 10 := by omega
  
  cases' h₁ with h₁ h₁
  
  · -- Case x ≤ 9
    interval_cases x <;> norm_num at h ⊢ <;>
      (try omega) <;>
      (try {
        have : y ≤ 11 := by
          nlinarith [pow_pos hy 3]
        interval_cases y <;> norm_num at h ⊢ <;> omega
      })
  
  · -- Case x ≥ 10
    have h₂ : (x + 2) ^ 3 < y ^ 3 := by
      have : (x + 2) ^ 3 = x ^ 3 + 6 * x ^ 2 + 12 * x + 8 := by ring
      rw [this]
      have : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := h
      rw [this]
      have : 0 < 2 * x ^ 2 - 18 * x := by
        have : 2 * x ^ 2 - 18 * x = 2 * x * (x - 9) := by ring
        rw [this]
        have : x - 9 ≥ 1 := by omega
        nlinarith
      nlinarith
    
    have h₃ : y ^ 3 < (x + 3) ^ 3 := by
      have : (x + 3) ^ 3 = x ^ 3 + 9 * x ^ 2 + 27 * x + 27 := by ring
      rw [this]
      have : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := h
      rw [this]
      have : 0 < x ^ 2 + 33 * x + 19 := by
        nlinarith
      nlinarith
    
    have h₄ : x + 2 < y := by
      apply Nat.pow_lt_pow_of_lt_left
      · omega
      · omega
      · exact h₂
    
    have h₅ : y < x + 3 := by
      apply Nat.pow_lt_pow_of_lt_left
      · omega
      · omega
      · exact h₃
    
    omega
