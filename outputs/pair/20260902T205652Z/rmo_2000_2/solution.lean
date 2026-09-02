import Mathlib

theorem rmo_2000_2
  (x y : ℕ)
  (hx : 0 < x)
  (hy : 0 < y)
  (h : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8) :
  x = 9 ∧ y = 11 := by
  by_cases hx_gt : x > 9
  · -- Case x > 9: Show no solution exists
    have h_lower : (x + 2) ^ 3 < x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := by
      have h1 : 2 * x * (x - 9) > 0 := by
        have h2 : x ≥ 10 := by omega
        have h3 : x - 9 ≥ 1 := by omega
        have h4 : 2 * x > 0 := by omega
        have h5 : x - 9 > 0 := by omega
        nlinarith
      calc
        (x + 2) ^ 3 = x ^ 3 + 6 * x ^ 2 + 12 * x + 8 := by ring
        _ < x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := by
          have h2 : 6 * x ^ 2 + 12 * x < 8 * x ^ 2 - 6 * x := by
            have h3 : 2 * x ^ 2 - 18 * x > 0 := by
              have h4 : x ≥ 10 := by omega
              nlinarith
            omega
          omega
    
    have h_upper : x ^ 3 + 8 * x ^ 2 - 6 * x + 8 < (x + 3) ^ 3 := by
      have h1 : x ^ 2 + 33 * x + 19 > 0 := by
        nlinarith
      calc
        x ^ 3 + 8 * x ^ 2 - 6 * x + 8 < x ^ 3 + 9 * x ^ 2 + 27 * x + 27 := by
          have h2 : 8 * x ^ 2 - 6 * x < 9 * x ^ 2 + 27 * x + 27 := by
            nlinarith
          omega
        _ = (x + 3) ^ 3 := by ring
    
    have h_y_bound : (x + 2) ^ 3 < y ^ 3 ∧ y ^ 3 < (x + 3) ^ 3 := by
      constructor
      · rw [h]
        exact h_lower
      · rw [h]
        exact h_upper
    
    have h_contradiction : False := by
      have h1 : x + 2 < y := by
        exact Nat.pow_lt_pow_of_lt_left h_y_bound.1 (by norm_num)
      have h2 : y < x + 3 := by
        exact Nat.lt_of_pow_lt_pow_left (by norm_num) h_y_bound.2
      omega
    
    contradiction
  · -- Case x ≤ 9: Check each case
    have hx_le : x ≤ 9 := by omega
    interval_cases x <;> norm_num at h ⊢ <;>
      (try omega) <;>
      (try {
        have : y ≤ 20 := by
          have : y ^ 3 ≤ 20 ^ 3 := by
            norm_num at h ⊢
            omega
          exact Nat.pow_le_pow_of_le_left (by omega) 3
        interval_cases y <;> norm_num at h ⊢ <;> omega
      })
