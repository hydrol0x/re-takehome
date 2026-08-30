import Mathlib

theorem rmo_2000_2
  (x y : ℕ)
  (hx : 0 < x)
  (hy : 0 < y)
  (h : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8) :
  x = 9 ∧ y = 11 := by
  -- First handle the case where x < 9 by checking each possibility
  have h_x_cases : x ≤ 8 → False := by
    intro h_x_le_8
    interval_cases x <;> norm_num at h ⊢ <;>
      (try omega) <;>
      (try {
        have : y ≤ 10 := by
          nlinarith [pow_pos hy 3]
        interval_cases y <;> norm_num at h ⊢ <;> omega
      })
  
  -- So x ≥ 9
  have h_x_ge_9 : x ≥ 9 := by
    by_contra h_lt
    exact h_x_cases (by omega)
  
  -- Now consider whether x = 9 or x > 9
  have h_x_eq_9_or_gt_9 : x = 9 ∨ x > 9 := by omega
  
  cases' h_x_eq_9_or_gt_9 with h_eq h_gt
  · -- Case x = 9
    subst h_eq
    have : y = 11 := by
      rw [← Nat.pow_succ]
      norm_num at h ⊢
      omega
    exact ⟨by rfl, this⟩
  · -- Case x > 9
    have h_contradiction : False := by
      -- Show (x+2)^3 < y^3 when x > 9
      have h_y_gt_x_plus_2 : x + 2 < y := by
        have : (x + 2) ^ 3 < y ^ 3 := by
          have : 2 * x * (x - 9) > 0 := by
            have : x - 9 > 0 := by omega
            nlinarith
          calc
            (x + 2) ^ 3 = x ^ 3 + 6 * x ^ 2 + 12 * x + 8 := by ring
            _ < x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := by
              nlinarith
            _ = y ^ 3 := by rw [h]
        exact Nat.lt_of_lt_of_le this (Nat.le_of_lt_succ _)
      
      -- Show y^3 < (x+3)^3 always
      have h_y_lt_x_plus_3 : y < x + 3 := by
        have : y ^ 3 < (x + 3) ^ 3 := by
          have : x ^ 2 + 33 * x + 19 > 0 := by nlinarith
          calc
            y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := by rw [h]
            _ < x ^ 3 + 9 * x ^ 2 + 27 * x + 27 := by
              nlinarith
            _ = (x + 3) ^ 3 := by ring
        exact Nat.lt_of_lt_of_le this (Nat.le_of_lt_succ _)
      
      -- This gives x + 2 < y < x + 3, impossible for integers
      omega
    
    exfalso
    exact h_contradiction
