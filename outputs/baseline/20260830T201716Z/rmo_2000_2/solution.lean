import Mathlib

open Nat Int

theorem rmo_2000_2
  (x y : ℕ)
  (hx : 0 < x)
  (hy : 0 < y)
  (h : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8) :
  x = 9 ∧ y = 11 := by
  have h_int : (y : ℤ) ^ 3 = (x : ℤ) ^ 3 + 8 * (x : ℤ) ^ 2 - 6 * (x : ℤ) + 8 := by
    norm_cast at h ⊢
    <;> simp [pow_two, pow_three] at h ⊢
    <;> ring_nf at h ⊢
    <;> linarith
  
  have h_cases : x < 9 ∨ x = 9 ∨ 9 < x := by omega
  
  rcases h_cases with (hlt | heq | hgt)
  
  · -- Case x < 9
    have h1 : (x + 1 : ℤ) ^ 3 < (y : ℤ) ^ 3 := by
      rw [← h_int]
      have h_diff : (5 : ℤ) * (x : ℤ) ^ 2 - 9 * (x : ℤ) + 7 > 0 := by
        have hx' : (x : ℤ) ≥ 1 := by exact_mod_cast hx
        nlinarith [sq_nonneg ((x : ℤ) - 1)]
      ring_nf at h_diff ⊢
      linarith
    
    have h2 : (y : ℤ) ^ 3 < (x + 2 : ℤ) ^ 3 := by
      rw [← h_int]
      have h_diff : (2 : ℤ) * (x : ℤ) ^ 2 - 18 * (x : ℤ) < 0 := by
        have hx' : (x : ℤ) ≤ 8 := by exact_mod_cast hlt
        have hx_ge : (x : ℤ) ≥ 1 := by exact_mod_cast hx
        nlinarith
      ring_nf at h_diff ⊢
      linarith
      
    have h_y_bounds : (x + 1 : ℤ) < (y : ℤ) ∧ (y : ℤ) < (x + 2 : ℤ) := by
      constructor
      · have h_ab : (x + 1 : ℤ) < (y : ℤ) := (pow_lt_pow_iff_right (by positivity) (by positivity) (by decide)).mp h1
        exact h_ab
      · have h_ab : (y : ℤ) < (x + 2 : ℤ) := (pow_lt_pow_iff_right (by positivity) (by positivity) (by decide)).mp h2
        exact h_ab
        
    have h_contra : False := by
      have h_y_int : (y : ℤ) = (x : ℤ) + 1 := by
        have h_le : (y : ℤ) ≤ (x : ℤ) + 1 := by linarith [h_y_bounds.2]
        have h_ge : (y : ℤ) ≥ (x : ℤ) + 1 := by linarith [h_y_bounds.1]
        linarith
      linarith [h_y_bounds.2]
      
    exfalso
    exact h_contra

  · -- Case x = 9
    subst heq
    have h_subst : y ^ 3 = 9 ^ 3 + 8 * 9 ^ 2 - 6 * 9 + 8 := by simpa using h
    norm_num at h_subst
    have h_y_val : y = 11 := by
      have : y ^ 3 = 1331 := by simpa using h_subst
      have : y ≤ 11 := by
        by_contra h_not
        have : y ≥ 12 := by omega
        have : y ^ 3 ≥ 12 ^ 3 := by gcongr
        norm_num at this
        linarith
      have : y ≥ 11 := by
        by_contra h_not
        have : y ≤ 10 := by omega
        have : y ^ 3 ≤ 10 ^ 3 := by gcongr
        norm_num at this
        linarith
      omega
    exact ⟨rfl, h_y_val⟩

  · -- Case x > 9
    have h1 : (x + 2 : ℤ) ^ 3 < (y : ℤ) ^ 3 := by
      rw [← h_int]
      have h_diff : (2 : ℤ) * (x : ℤ) ^ 2 - 18 * (x : ℤ) > 0 := by
        have hx_gt : (x : ℤ) ≥ 10 := by exact_mod_cast hgt
        nlinarith
      ring_nf at h_diff ⊢
      linarith
      
    have h2 : (y : ℤ) ^ 3 < (x + 3 : ℤ) ^ 3 := by
      rw [← h_int]
      have h_diff : (x : ℤ) ^ 2 + 33 * (x : ℤ) + 19 > 0 := by
        have hx_pos : (x : ℤ) ≥ 10 := by exact_mod_cast hgt
        nlinarith
      ring_nf at h_diff ⊢
      linarith
      
    have h_y_bounds : (x + 2 : ℤ) < (y : ℤ) ∧ (y : ℤ) < (x + 3 : ℤ) := by
      constructor
      · have h_ab : (x + 2 : ℤ) < (y : ℤ) := (pow_lt_pow_iff_right (by positivity) (by positivity) (by decide)).mp h1
        exact h_ab
      · have h_ab : (y : ℤ) < (x + 3 : ℤ) := (pow_lt_pow_iff_right (by positivity) (by positivity) (by decide)).mp h2
        exact h_ab
        
    have h_contra : False := by
      have h_y_int : (y : ℤ) = (x : ℤ) + 2 := by
        have h_le : (y : ℤ) ≤ (x : ℤ) + 2 := by linarith [h_y_bounds.2]
        have h_ge : (y : ℤ) ≥ (x : ℤ) + 2 := by linarith [h_y_bounds.1]
        linarith
      linarith [h_y_bounds.2]
      
    exfalso
    exact h_contra
