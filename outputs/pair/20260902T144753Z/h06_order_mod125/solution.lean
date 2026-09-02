import Mathlib

/-- The multiplicative order of `2` modulo `125`. Must be a numeric literal. -/
abbrev h06_answer : ℕ := 100

/-- `h06_answer` is the least positive `n` with `2 ^ n ≡ 1 (mod 125)`. -/
theorem h06_order_mod125 :
    IsLeast {n : ℕ | 0 < n ∧ 2 ^ n % 125 = 1} h06_answer := by
  constructor
  · -- Show 100 is in the set
    constructor
    · norm_num
    · norm_num
  · -- Show 100 is minimal
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    cases' hn with hn_pos hn_mod
    by_contra h_not_le
    push_neg at h_not_le
    have h_lt : n < 100 := by omega
    
    -- Check that no smaller n works by computing key powers
    have h_key : ∀ k : ℕ, 0 < k → k < 100 → 2 ^ k % 125 ≠ 1 := by
      intro k hk_pos hk_lt
      have : k ≤ 99 := by omega
      interval_cases k <;> norm_num at hk_lt ⊢ <;> try contradiction
      <;> norm_num
      <;> omega
    
    exact h_key n hn_pos h_lt hn_mod
