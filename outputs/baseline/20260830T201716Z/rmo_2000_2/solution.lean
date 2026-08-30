import Mathlib

theorem rmo_2000_2
  (x y : ℕ)
  (hx : 0 < x)
  (hy : 0 < y)
  (h : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8) :
  x = 9 ∧ y = 11 := by
  have h₁ : x ≤ 9 := by
    by_contra! hx'
    have h₂ : x ≥ 10 := by linarith
    have h₃ : (x + 2) ^ 3 < y ^ 3 := by
      have h₄ : (x + 2) ^ 3 = x ^ 3 + 6 * x ^ 2 + 12 * x + 8 := by ring
      rw [h₄]
      have h₅ : x ^ 3 + 6 * x ^ 2 + 12 * x + 8 < x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := by
        have h₆ : 0 < 2 * x ^ 2 - 18 * x := by
          nlinarith
        omega
      linarith
    have h₄ : y ^ 3 < (x + 3) ^ 3 := by
      have h₅ : (x + 3) ^ 3 = x ^ 3 + 9 * x ^ 2 + 27 * x + 27 := by ring
      rw [h₅]
      have h₆ : x ^ 3 + 8 * x ^ 2 - 6 * x + 8 < x ^ 3 + 9 * x ^ 2 + 27 * x + 27 := by
        have h₇ : 0 < x ^ 2 + 33 * x + 19 := by nlinarith
        omega
      linarith
    have h₅ : x + 2 < y := by
      exact Nat.lt_of_lt_of_le (by simpa using h₃) (by simp)
    have h₆ : y < x + 3 := by
      exact Nat.lt_of_lt_of_le (by simpa using h₄) (by simp)
    have h₇ : y ≤ x + 2 := by linarith
    linarith
  
  interval_cases x <;> norm_num at h ⊢ <;>
    (try omega) <;>
    (try {
      have : y ≤ 20 := by
        by_contra! hy'
        have : y ≥ 21 := by omega
        have : y ^ 3 ≥ 21 ^ 3 := by
          exact Nat.pow_le_pow_of_le_left (by omega) 3
        norm_num at this ⊢
        omega
      interval_cases y <;> norm_num at h ⊢ <;> omega
    }) <;>
    (try {
      have : y ≤ 15 := by
        by_contra! hy'
        have : y ≥ 16 := by omega
        have : y ^ 3 ≥ 16 ^ 3 := by
          exact Nat.pow_le_pow_of_le_left (by omega) 3
        norm_num at this ⊢
        omega
      interval_cases y <;> norm_num at h ⊢ <;> omega
    })
