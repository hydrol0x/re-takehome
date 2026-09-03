import Mathlib

/-- The least positive integer `n` such that `11` divides `3 ^ n - 1`.
Must be a numeric literal. -/
abbrev c07_answer : ℕ := 5

/-- `c07_answer` is the least element of the set of positive `n` with `11 ∣ 3 ^ n - 1`. -/
theorem c07_order_three :
    IsLeast {n : ℕ | 0 < n ∧ 11 ∣ 3 ^ n - 1} c07_answer := by
  constructor
  · -- Prove that 5 is in the set (0 < 5 and 11 ∣ 3^5 - 1)
    constructor
    · norm_num
    · norm_num [Nat.dvd_iff_mod_eq_zero]
  · -- Prove that 5 is a lower bound for the set
    intro n hn
    have h₁ : 0 < n := hn.1
    have h₂ : 11 ∣ 3 ^ n - 1 := hn.2
    by_contra h
    -- If n < 5, then n ∈ {1, 2, 3, 4}
    have h₃ : n < 5 := by omega
    interval_cases n <;> norm_num at h₂ ⊢ <;>
      (try contradiction) <;>
      (try omega)
