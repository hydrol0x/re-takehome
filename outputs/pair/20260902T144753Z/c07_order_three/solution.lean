import Mathlib

/-- The least positive integer `n` such that `11` divides `3 ^ n - 1`.
Must be a numeric literal. -/
abbrev c07_answer : ℕ := 5

/-- `c07_answer` is the least element of the set of positive `n` with `11 ∣ 3 ^ n - 1`. -/
theorem c07_order_three :
    IsLeast {n : ℕ | 0 < n ∧ 11 ∣ 3 ^ n - 1} c07_answer := by
  constructor
  · -- Prove 5 is in the set
    constructor
    · -- 0 < 5
      norm_num
    · -- 11 ∣ 3^5 - 1
      norm_num [Nat.dvd_iff_mod_eq_zero]
  · -- Prove 5 is minimal
    intro n hn
    have h₁ : 0 < n := hn.1
    have h₂ : 11 ∣ 3 ^ n - 1 := hn.2
    by_contra h
    -- If not (5 ≤ n), then n < 5
    have h₃ : n < 5 := lt_of_not_ge h
    -- Check each possible value of n from 1 to 4
    interval_cases n <;> norm_num at h₂ ⊢ <;> omega
