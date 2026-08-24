import Mathlib

lemma h_lower_bound (x : ℕ) (hx : 0 < x) (y : ℕ) 
    (h_eq : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8) :
    (x + 1) ^ 3 < y ^ 3 := by cases x with
    | zero => contradiction
    | succ x' =>
      simp [pow_succ, Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib] at h_eq ⊢
      ring_nf at h_eq ⊢
      omega

lemma h_upper_bound (x : ℕ) (hx : 0 < x) (y : ℕ) 
    (h_eq : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8) :
    y ^ 3 < (x + 3) ^ 3 := by calc
        y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := h_eq
        _ < x ^ 3 + 9 * x ^ 2 + 27 * x + 27 := by
          cases x with
          | zero => contradiction
          | succ x' =>
            simp [pow_succ, Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib]
            ring_nf
            omega
        _ = (x + 3) ^ 3 := by ring

lemma h_cube_bounds_combined (x : ℕ) (hx : 0 < x) (y : ℕ) 
    (h_eq : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8) :
    (x + 1) ^ 3 < y ^ 3 ∧ y ^ 3 < (x + 3) ^ 3 := by exact ⟨h_lower_bound x hx y h_eq, h_upper_bound x hx y h_eq⟩

lemma h_y_gt_x_plus_1 (x : ℕ) (hx : 0 < x) (y : ℕ) 
    (h_bounds : (x + 1) ^ 3 < y ^ 3 ∧ y ^ 3 < (x + 3) ^ 3) :
    x + 1 < y := by cases lt_or_ge (x + 1) y with
    | inl h => exact h
    | inr h =>
      have : y ^ 3 ≤ (x + 1) ^ 3 := Nat.pow_le_pow_left h 3
      linarith [h_bounds.1]

lemma h_y_lt_x_plus_3 (x : ℕ) (hx : 0 < x) (y : ℕ) 
    (h_bounds : (x + 1) ^ 3 < y ^ 3 ∧ y ^ 3 < (x + 3) ^ 3) :
    y < x + 3 := by cases lt_or_ge y (x + 3) with
    | inl h => exact h
    | inr h =>
      have h_cube : (x + 3) ^ 3 ≤ y ^ 3 := by
        calc
          (x + 3) ^ 3 = (x + 3) * (x + 3) * (x + 3) := by ring
          _ ≤ y * (x + 3) * (x + 3) := by gcongr
          _ ≤ y * y * (x + 3) := by gcongr
          _ ≤ y * y * y := by gcongr
          _ = y ^ 3 := by ring
      linarith [h_bounds.2, h_cube]

lemma h_y_equals_x_plus_two (x : ℕ) (hx : 0 < x) (y : ℕ)
    (_ : 0 < y)
    (h_xy : x + 1 < y ∧ y < x + 3) :
    y = x + 2 := by linarith

lemma h_substitute_y (x : ℕ) (y : ℕ) (h_y_eq : y = x + 2) :
    y ^ 3 = x ^ 3 + 6 * x ^ 2 + 12 * x + 8 := by calc
      y ^ 3 = (x + 2) ^ 3 := by rw [h_y_eq]
      _ = x ^ 3 + 6 * x ^ 2 + 12 * x + 8 := by ring

lemma h_quadratic_equation (x : ℕ) (hx : 0 < x) (y : ℕ)
    (h_eq : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8)
    (h_y_eq : y = x + 2) :
    2 * x ^ 2 = 18 * x := by calc
      2 * x ^ 2 = 2 * x ^ 2 := rfl
      _ = 18 * x := by
        rw [h_y_eq] at h_eq
        ring_nf at h_eq
        have h : 6 * x ^ 2 + 12 * x = 8 * x ^ 2 - 6 * x := by
          simp [pow_two, pow_three] at h_eq ⊢
          ring_nf at h_eq ⊢
          omega
        omega

lemma h_solve_quadratic (x : ℕ) (hx_pos : 0 < x) (h_quad : 2 * x ^ 2 = 18 * x) :
    x = 9 := by nlinarith

lemma h_final_value_y (x : ℕ) (hx_eq : x = 9) (y : ℕ) (h_y_eq : y = x + 2) :
    y = 11 := by linarith

theorem rmo_2000_2
  (x y : ℕ)
  (hx : 0 < x)
  (hy : 0 < y)
  (h : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8) :
  x = 9 ∧ y = 11 := by
  have h_bounds : (x + 1) ^ 3 < y ^ 3 ∧ y ^ 3 < (x + 3) ^ 3 := 
    h_cube_bounds_combined x hx y h
  have h_xy : x + 1 < y ∧ y < x + 3 := by
    constructor
    · exact h_y_gt_x_plus_1 x hx y h_bounds
    · exact h_y_lt_x_plus_3 x hx y h_bounds
  have h_y_eq : y = x + 2 := 
    h_y_equals_x_plus_two x hx y hy h_xy
  have h_quad : 2 * x ^ 2 = 18 * x := 
    h_quadratic_equation x hx y h h_y_eq
  have h_x_eq : x = 9 := 
    h_solve_quadratic x hx h_quad
  have h_y_final : y = 11 := 
    h_final_value_y x h_x_eq y h_y_eq
  exact ⟨h_x_eq, h_y_final⟩
