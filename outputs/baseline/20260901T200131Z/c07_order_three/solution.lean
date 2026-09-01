import Mathlib

/-- The least positive integer `n` such that `11` divides `3 ^ n - 1`.
Must be a numeric literal. -/
abbrev c07_answer : ℕ := 5

/-- `c07_answer` is the least element of the set of positive `n` with `11 ∣ 3 ^ n - 1`. -/
theorem c07_order_three :
    IsLeast {n : ℕ | 0 < n ∧ 11 ∣ 3 ^ n - 1} c07_answer := by
  constructor
  · -- Show that 5 is in the set
    constructor
    · -- 0 < 5
      norm_num
    · -- 11 ∣ 3^5 - 1
      norm_num [Nat.dvd_iff_mod_eq_zero]
  · -- Show that 5 is the least element
    intro b hb
    have h1 : 0 < b := hb.1
    have h2 : 11 ∣ 3 ^ b - 1 := hb.2
    -- We need to show 5 ≤ b
    by_contra h
    -- If 5 > b, then b < 5
    have h3 : b < 5 := lt_of_not_ge h
    -- Since b > 0 and b < 5, check each case
    interval_cases b <;> simp_all (config := {decide := true})
