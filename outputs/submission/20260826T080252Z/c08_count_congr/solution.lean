import Mathlib

/-- The number of natural numbers `n < 250` with `n % 3 = 0` and `n % 5 = 2`.
Must be a numeric literal. -/
abbrev c08_answer : ℕ := 16

/-- Count the `n < 250` that are divisible by `3` and leave remainder `2` mod `5`. -/
theorem c08_count_congr :
    (Finset.filter (fun n => n % 3 = 0 ∧ n % 5 = 2) (Finset.range 250)).card
      = c08_answer := by
  rfl
