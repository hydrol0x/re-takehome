import Mathlib

/-- The multiplicative order of `2` modulo `125`. Must be a numeric literal. -/
abbrev h06_answer : ℕ := 100

/-- `h06_answer` is the least positive `n` with `2 ^ n ≡ 1 (mod 125)`. -/
theorem h06_order_mod125 :
    IsLeast {n : ℕ | 0 < n ∧ 2 ^ n % 125 = 1} h06_answer := by
  constructor
  · constructor
    · norm_num
    · norm_num [Nat.pow_mod]
  · intro m hm
    have h₁ : 0 < m := hm.1
    have h₂ : 2 ^ m % 125 = 1 := hm.2
    by_contra h
    have h₃ : m < 100 := by omega
    -- Verify that no m < 100 satisfies the condition
    revert m h₁ h₂ h₃
    decide
