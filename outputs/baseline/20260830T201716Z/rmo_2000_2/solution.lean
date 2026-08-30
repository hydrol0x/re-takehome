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
        nlinarith
      linarith
    have h₄ : y ^ 3 < (x + 3) ^ 3 := by
      have h₅ : (x + 3) ^ 3 = x ^ 3 + 9 * x ^ 2 + 27 * x + 27 := by ring
      rw [h₅]
      have h₆ : x ^ 3 + 8 * x ^ 2 - 6 * x + 8 < x ^ 3 + 9 * x ^ 2 + 27 * x + 27 := by
        nlinarith
      linarith
    have h₅ : x + 2 < y := by
      exact Nat.lt_of_pow_lt_pow_left hy h₃
    have h₆ : y < x + 3 := by
      exact Nat.lt_of_pow_lt_pow_left hy h₄
    have h₇ : y = x + 2 := by omega
    rw [h₇] at h
    ring_nf at h
    have h₈ : (x + 2) ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := by
      linarith
    have h₉ : x ^ 3 + 6 * x ^ 2 + 12 * x + 8 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := by
      linarith
    have h₁₀ : 6 * x ^ 2 + 12 * x = 8 * x ^ 2 - 6 * x := by
      linarith
    have h₁₁ : 2 * x ^ 2 - 18 * x = 0 := by
      linarith
    have h₁₂ : x * (2 * x - 18) = 0 := by
      linarith
    have h₁₃ : x = 0 ∨ 2 * x - 18 = 0 := by
      apply eq_zero_or_eq_zero_of_mul_eq_zero h₁₂
    cases h₁₃ with
    | inl h₁₄ =>
      linarith
    | inr h₁₄ =>
      have h₁₅ : 2 * x = 18 := by omega
      have h₁₆ : x = 9 := by omega
      linarith
  interval_cases x <;> norm_num at h ⊢ <;>
    (try omega) <;>
    (try {
      have h₂ : y ≤ 15 := by
        nlinarith
      interval_cases y <;> norm_num at h ⊢ <;> omega
    })
