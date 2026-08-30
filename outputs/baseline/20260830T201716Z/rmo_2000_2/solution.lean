import Mathlib

theorem rmo_2000_2
  (x y : ℕ)
  (hx : 0 < x)
  (hy : 0 < y)
  (h : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8) :
  x = 9 ∧ y = 11 := by
  have h₁ : y ≥ x + 2 := by
    have h₂ : y ^ 3 ≥ (x + 1) ^ 3 + 1 := by
      calc
        y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := h
        _ ≥ (x + 1) ^ 3 + 1 := by
          cases x with
          | zero => contradiction
          | succ x' =>
            simp [pow_succ, Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib] at h ⊢
            ring_nf at h ⊢
            omega
    have h₃ : y ≥ x + 2 := by
      by_contra h₄
      have h₅ : y ≤ x + 1 := by omega
      have h₆ : y ^ 3 ≤ (x + 1) ^ 3 := by
        exact Nat.pow_le_pow_of_le_left h₅ 3
      omega
    exact h₃
  
  have h₂ : ¬(x < 9) := by
    intro h₃
    have h₄ : x ≤ 8 := by omega
    have h₅ : y ≤ x + 1 := by
      have h₆ : y ^ 3 < (x + 2) ^ 3 := by
        calc
          y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := h
          _ < (x + 2) ^ 3 := by
            cases x with
            | zero => contradiction
            | succ x' =>
              simp [pow_succ, Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib] at h ⊢
              ring_nf at h ⊢
              have h₇ : 0 < x + 1 := by omega
              nlinarith
      have h₇ : y < x + 2 := by
        by_contra h₈
        have h₉ : y ≥ x + 2 := by omega
        have h₁₀ : y ^ 3 ≥ (x + 2) ^ 3 := by
          exact Nat.pow_le_pow_of_le_left h₉ 3
        omega
      omega
    have h₆ : y ≥ x + 2 := h₁
    omega
  
  have h₃ : ¬(x > 9) := by
    intro h₄
    have h₅ : x ≥ 10 := by omega
    have h₆ : y ≥ x + 3 := by
      have h₇ : y ^ 3 > (x + 2) ^ 3 := by
        calc
          y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := h
          _ > (x + 2) ^ 3 := by
            cases x with
            | zero => contradiction
            | succ x' =>
              simp [pow_succ, Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib] at h ⊢
              ring_nf at h ⊢
              have h₈ : 0 < x + 1 := by omega
              nlinarith
      have h₈ : y > x + 2 := by
        by_contra h₉
        have h₁₀ : y ≤ x + 2 := by omega
        have h₁₁ : y ^ 3 ≤ (x + 2) ^ 3 := by
          exact Nat.pow_le_pow_of_le_left h₁₀ 3
        omega
      omega
    have h₇ : y ≤ x + 2 := by
      have h₈ : y ^ 3 < (x + 3) ^ 3 := by
        calc
          y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := h
          _ < (x + 3) ^ 3 := by
            cases x with
            | zero => contradiction
            | succ x' =>
              simp [pow_succ, Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib] at h ⊢
              ring_nf at h ⊢
              have h₉ : 0 < x + 1 := by omega
              nlinarith
      have h₉ : y < x + 3 := by
        by_contra h₁₀
        have h₁₁ : y ≥ x + 3 := by omega
        have h₁₂ : y ^ 3 ≥ (x + 3) ^ 3 := by
          exact Nat.pow_le_pow_of_le_left h₁₁ 3
        omega
      omega
    omega
  
  have h₄ : x = 9 := by
    by_contra h₅
    have h₆ : x ≠ 9 := h₅
    have h₇ : x < 9 ∨ x > 9 := by
      cases lt_or_gt_of_ne h₆
      <;> simp_all
    cases h₇ with
    | inl h₇ =>
      exact h₂ h₇
    | inr h₇ =>
      exact h₃ h₇
  
  have h₅ : y = 11 := by
    rw [h₄] at h
    norm_num at h
    have h₆ : y = 11 := by
      have h₇ : y ^ 3 = 1331 := by
        norm_num at h ⊢
        <;> linarith
      have h₈ : y ≤ 11 := by
        by_contra h₉
        have h₁₀ : y ≥ 12 := by omega
        have h₁₁ : y ^ 3 ≥ 12 ^ 3 := by
          exact Nat.pow_le_pow_of_le_left h₁₀ 3
        norm_num at h₁₁
        omega
      have h₉ : y ≥ 11 := by
        by_contra h₁₀
        have h₁₁ : y ≤ 10 := by omega
        have h₁₂ : y ^ 3 ≤ 10 ^ 3 := by
          exact Nat.pow_le_pow_of_le_left h₁₁ 3
        norm_num at h₁₂
        omega
      omega
    exact h₆
  
  exact ⟨h₄, h₅⟩
