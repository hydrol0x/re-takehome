import Mathlib

theorem rmo_2000_2
  (x y : ℕ)
  (hx : 0 < x)
  (hy : 0 < y)
  (h : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8) :
  x = 9 ∧ y = 11 := by
  have hle : 6 * x ≤ x ^ 3 + 8 * x ^ 2 := by nlinarith
  zify [hle] at h
  have hx' : (0 : ℤ) < (x : ℤ) := by exact_mod_cast hx
  -- y is strictly between x+1 and x+3, because (x+1)^3 < y^3 < (x+3)^3
  have hlow : x + 1 < y := by
    by_contra hc
    push_neg at hc
    have h3 : y ^ 3 ≤ (x + 1) ^ 3 := Nat.pow_le_pow_left hc 3
    zify at h3
    nlinarith [h, h3, hx']
  have hhigh : y < x + 3 := by
    by_contra hc
    push_neg at hc
    have h3 : (x + 3) ^ 3 ≤ y ^ 3 := Nat.pow_le_pow_left hc 3
    zify at h3
    nlinarith [h, h3, hx']
  have hy2 : y = x + 2 := by omega
  subst hy2
  push_cast at h
  -- (x+2)^3 = x^3 + 8x^2 - 6x + 8  ==>  2x^2 = 18x  ==>  x = 9
  have h2 : (x : ℤ) * ((x : ℤ) - 9) = 0 := by nlinarith [h]
  have hx9 : (x : ℤ) = 9 := by
    rcases mul_eq_zero.mp h2 with h0 | h9
    · linarith
    · linarith
  have : x = 9 := by exact_mod_cast hx9
  exact ⟨this, by omega⟩
