import Mathlib

/-- The least positive integer `n` such that `11` divides `3 ^ n - 1`.
Must be a numeric literal. -/
abbrev c07_answer : ℕ := 5

/-- `c07_answer` is the least element of the set of positive `n` with `11 ∣ 3 ^ n - 1`. -/
theorem c07_order_three :
    IsLeast {n : ℕ | 0 < n ∧ 11 ∣ 3 ^ n - 1} c07_answer := by
  constructor
  · -- Prove that 5 is in the set (0 < 5 ∧ 11 ∣ 3^5 - 1)
    constructor
    · norm_num
    · norm_num [Nat.dvd_iff_mod_eq_zero]
      <;> decide
  · -- Prove that 5 is a lower bound for the set
    intro n hn
    have h1 : 0 < n := hn.1
    have h2 : 11 ∣ 3 ^ n - 1 := hn.2
    by_contra h
    -- If n < 5, check each case
    have h3 : n < 5 := lt_of_not_ge h
    interval_cases n <;> norm_num at h2 ⊢ <;> contradiction
