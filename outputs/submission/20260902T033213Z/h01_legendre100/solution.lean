import Mathlib

/-- The largest `k` such that `3 ^ k ∣ 100!`. Must be a numeric literal. -/
abbrev h01_answer : ℕ := 48

/-- `h01_answer` is the greatest `k` with `3 ^ k` dividing `100!`. -/
theorem h01_legendre100 :
    IsGreatest {k : ℕ | 3 ^ k ∣ Nat.factorial 100} h01_answer := by
  constructor
  · -- Show 48 is in the set: 3^48 divides 100!
    have h : 3 ^ 48 ∣ Nat.factorial 100 := by
      norm_num [Nat.factorial]
      <;> decide
    exact h
  · -- Show 48 is an upper bound: if 3^k divides 100!, then k ≤ 48
    intro k hk
    have h₁ : 3 ^ k ∣ Nat.factorial 100 := hk
    -- Use the fact that the exponent of 3 in 100! is exactly 48
    -- This comes from Legendre's formula: floor(100/3) + floor(100/9) + floor(100/27) + floor(100/81) = 33 + 11 + 3 + 1 = 48
    have h₂ : k ≤ 48 := by
      -- By contradiction: if k > 48, then 3^(49) would divide 100!, but it doesn't
      by_contra h₃
      -- If k > 48, then k ≥ 49
      have h₄ : k ≥ 49 := by omega
      -- So 3^49 divides 3^k which divides 100!
      have h₅ : 3 ^ 49 ∣ Nat.factorial 100 := by
        have h₆ : 3 ^ k ∣ Nat.factorial 100 := h₁
        have h₇ : 3 ^ 49 ∣ 3 ^ k := by
          apply pow_dvd_pow _
          omega
        exact dvd_trans h₇ h₆
      -- But 3^49 does not divide 100! (the exponent of 3 in 100! is only 48)
      norm_num at h₅
      <;> decide
    exact h₂
