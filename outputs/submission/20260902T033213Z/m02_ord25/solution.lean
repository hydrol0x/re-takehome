import Mathlib

/-- The least positive integer `n` such that `2 ^ n` leaves remainder `1` when
divided by `25`. Must be a numeric literal. -/
abbrev m02_answer : ℕ := 20

/-- `m02_answer` is the least element of the set of positive `n` with
`2 ^ n % 25 = 1`; that is, the multiplicative order of `2` modulo `25`. -/
theorem m02_ord25 : IsLeast {n : ℕ | 0 < n ∧ 2 ^ n % 25 = 1} m02_answer := by
  linarith
