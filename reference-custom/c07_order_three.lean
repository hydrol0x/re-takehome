import Mathlib

/-- The least positive integer `n` such that `11` divides `3 ^ n - 1`.
Must be a numeric literal. -/
abbrev c07_answer : ℕ := 5

/-- `c07_answer` is the least element of the set of positive `n` with `11 ∣ 3 ^ n - 1`. -/
theorem c07_order_three :
    IsLeast {n : ℕ | 0 < n ∧ 11 ∣ 3 ^ n - 1} c07_answer := by
  constructor
  · show 0 < 5 ∧ 11 ∣ 3 ^ 5 - 1
    norm_num
  · rintro n ⟨hn, hdvd⟩
    by_contra hlt
    push_neg at hlt
    have hlt5 : n < 5 := hlt
    interval_cases n <;> norm_num at hdvd
