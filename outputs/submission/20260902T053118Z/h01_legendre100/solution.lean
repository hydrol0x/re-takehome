import Mathlib

/-- The largest `k` such that `3 ^ k ∣ 100!`. Must be a numeric literal. -/
abbrev h01_answer : ℕ := 48

/-- `h01_answer` is the greatest `k` with `3 ^ k` dividing `100!`. -/
theorem h01_legendre100 :
    IsGreatest {k : ℕ | 3 ^ k ∣ Nat.factorial 100} h01_answer := by
  constructor
  · -- Prove 3^48 divides 100!
    have h : 3 ^ 48 ∣ Nat.factorial 100 := by
      -- Calculate the exponent of 3 in 100! using Legendre's formula
      -- floor(100/3) = 33
      -- floor(100/9) = 11  
      -- floor(100/27) = 3
      -- floor(100/81) = 1
      -- Total = 33 + 11 + 3 + 1 = 48
      norm_num [Nat.dvd_factorial]
      <;> decide
    simpa [h01_answer] using h
  · -- Prove that if 3^k divides 100!, then k ≤ 48
    intro k hk
    have h : 3 ^ k ∣ Nat.factorial 100 := by simpa [h01_answer] using hk
    -- Use Legendre's formula: the exponent of p in n! is sum of floor(n/p^i)
    -- We need to show k ≤ 48 where 48 = floor(100/3) + floor(100/9) + floor(100/27) + floor(100/81)
    have h_bound : k ≤ 48 := by
      -- If 3^k divides 100!, then k cannot exceed the exponent of 3 in 100!
      -- The exponent of 3 in 100! is exactly 48
      by_contra h_lt
      -- Assume k > 48, derive contradiction
      push_neg at h_lt
      have h_gt : k ≥ 49 := by omega
      -- Check that 3^49 does not divide 100!
      have h_div : ¬(3 ^ 49 ∣ Nat.factorial 100) := by
        norm_num [Nat.dvd_factorial]
        <;> decide
      -- Since 3^k divides 100! and k ≥ 49, we'd have 3^49 divides 100!
      have h_49 : 3 ^ 49 ∣ Nat.factorial 100 := by
        exact dvd_trans (pow_dvd_pow _ (by omega)) h
      contradiction
    exact h_bound
