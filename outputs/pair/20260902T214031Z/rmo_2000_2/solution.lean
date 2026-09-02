import Mathlib

theorem rmo_2000_2
  (x y : ℕ)
  (hx : 0 < x)
  (hy : 0 < y)
  (h : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8) :
  x = 9 ∧ y = 11 := by
  have h_y_ge_x : x ≤ y := by
    by_contra h_lt
    have h_y_lt_x : y < x := by omega
    have h_y_le_x_minus_1 : y ≤ x - 1 := by omega
    
    have h_left : y ^ 3 ≤ (x - 1) ^ 3 := by
      exact Nat.pow_le_pow_of_le_left h_y_le_x_minus_1 3
    
    have h_right : (x - 1) ^ 3 < x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := by
      cases x with
      | zero => contradiction
      | succ x' =>
        simp [Nat.pow_succ, Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib] at h_left ⊢
        ring_nf at h_left ⊢
        omega
    
    linarith
  
  have h_y_eq_x_plus_2 : y = x + 2 := by
    by_contra h_neq
    have h_y_ne_x_plus_2 : y ≠ x + 2 := h_neq
    
    have h_cases : y = x ∨ y ≥ x + 3 := by
      have h_y_ge_x : x ≤ y := h_y_ge_x
      have h_y_ne_x_plus_2 : y ≠ x + 2 := h_neq
      
      by_cases h_y_eq_x : y = x
      · exact Or.inl h_y_eq_x
      · right
        have h_y_gt_x : x < y := by
          contrapose! h_y_eq_x
          omega
        have h_y_ge_x_plus_1 : y ≥ x + 1 := by omega
        
        by_cases h_y_eq_x_plus_1 : y = x + 1
        · have h_y_eq_x_plus_1 : y = x + 1 := h_y_eq_x_plus_1
          have h_y_eq_x_plus_2 : y = x + 2 := by omega
          contradiction
        · have h_y_ge_x_plus_2 : y ≥ x + 2 := by omega
          have h_y_ge_x_plus_3 : y ≥ x + 3 := by omega
          exact h_y_ge_x_plus_3
    
    cases h_cases with
    | inl h_y_eq_x =>
      have h_y_eq_x : y = x := h_y_eq_x
      rw [h_y_eq_x] at h
      have h_eq : x ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := by simpa using h
      have h_pos : 0 < 8 * x ^ 2 - 6 * x + 8 := by
        have h_x_pos : 0 < x := hx
        have h_x_sq_pos : 0 < x ^ 2 := by positivity
        have h_8x_sq_pos : 0 < 8 * x ^ 2 := by positivity
        have h_6x_pos : 0 < 6 * x := by positivity
        have h_8_pos : 0 < 8 := by norm_num
        omega
      omega
    | inr h_y_ge_x_plus_3 =>
      have h_y_ge_x_plus_3 : y ≥ x + 3 := h_y_ge_x_plus_3
      have h_y_ge_x_plus_3_pow : y ^ 3 ≥ (x + 3) ^ 3 := by
        exact Nat.pow_le_pow_of_le_left h_y_ge_x_plus_3 3
      
      have h_rhs_bound : (x + 3) ^ 3 > x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := by
        cases x with
        | zero => contradiction
        | succ x' =>
          simp [Nat.pow_succ, Nat.mul_add, Nat.add_mul] at h_rhs_bound ⊢
          ring_nf at h_rhs_bound ⊢
          omega
      
      have h_contradiction : y ^ 3 > x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := by
        calc
          y ^ 3 ≥ (x + 3) ^ 3 := h_y_ge_x_plus_3_pow
          _ > x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := h_rhs_bound
      
      linarith
  
  have h_y_eq_x_plus_2 : y = x + 2 := h_y_eq_x_plus_2
  rw [h_y_eq_x_plus_2] at h
  have h_eq : (x + 2) ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := by simpa using h
  
  have h_expanded : x ^ 3 + 6 * x ^ 2 + 12 * x + 8 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := by
    calc
      x ^ 3 + 6 * x ^ 2 + 12 * x + 8 = (x + 2) ^ 3 := by ring
      _ = x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := by simpa [h_eq]
  
  have h_simplified : 6 * x ^ 2 + 12 * x = 8 * x ^ 2 - 6 * x := by
    have h_lhs : x ^ 3 + 6 * x ^ 2 + 12 * x + 8 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := h_expanded
    have h_sub : 6 * x ^ 2 + 12 * x = 8 * x ^ 2 - 6 * x := by
      have h_sub_lhs : x ^ 3 + 6 * x ^ 2 + 12 * x + 8 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := h_lhs
      have h_sub_rhs : 6 * x ^ 2 + 12 * x = 8 * x ^ 2 - 6 * x := by
        omega
      exact h_sub_rhs
    exact h_sub
  
  have h_quadratic : 2 * x ^ 2 - 18 * x = 0 := by
    have h_lhs : 6 * x ^ 2 + 12 * x = 8 * x ^ 2 - 6 * x := h_simplified
    have h_rhs : 2 * x ^ 2 - 18 * x = 0 := by
      omega
    exact h_rhs
  
  have h_factored : x * (x - 9) = 0 := by
    have h_lhs : 2 * x ^ 2 - 18 * x = 0 := h_quadratic
    have h_rhs : x * (x - 9) = 0 := by
      omega
    exact h_rhs
  
  have h_x_eq_9 : x = 9 := by
    have h_factored : x * (x - 9) = 0 := h_factored
    have h_x_pos : 0 < x := hx
    have h_x_eq_9 : x = 9 := by
      by_contra h_neq
      have h_x_ne_9 : x ≠ 9 := h_neq
      have h_x_lt_9_or_gt_9 : x < 9 ∨ x > 9 := by
        omega
      cases h_x_lt_9_or_gt_9 with
      | inl h_x_lt_9 =>
        have h_x_lt_9 : x < 9 := h_x_lt_9
        have h_x_pos : 0 < x := hx
        have h_x_nonzero : x ≠ 0 := by omega
        have h_x_minus_9_nonzero : x - 9 ≠ 0 := by
          have h_x_lt_9 : x < 9 := h_x_lt_9
          omega
        have h_product_nonzero : x * (x - 9) ≠ 0 := by
          apply mul_ne_zero
          · exact h_x_nonzero
          · exact h_x_minus_9_nonzero
        contradiction
      | inr h_x_gt_9 =>
        have h_x_gt_9 : x > 9 := h_x_gt_9
        have h_x_minus_9_pos : x - 9 > 0 := by omega
        have h_x_minus_9_nonzero : x - 9 ≠ 0 := by omega
        have h_product_nonzero : x * (x - 9) ≠ 0 := by
          apply mul_ne_zero
          · exact h_x_pos
          · exact h_x_minus_9_nonzero
        contradiction
    exact h_x_eq_9
  
  have h_y_eq_11 : y = 11 := by
    have h_y_eq_x_plus_2 : y = x + 2 := h_y_eq_x_plus_2
    have h_x_eq_9 : x = 9 := h_x_eq_9
    rw [h_x_eq_9] at h_y_eq_x_plus_2
    omega
  
  exact ⟨h_x_eq_9, h_y_eq_11⟩
