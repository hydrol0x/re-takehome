import Mathlib

/-- The remainder when `1! + 2! + ⋯ + 10!` is divided by `100`.
Must be a numeric literal. -/
abbrev c09_answer : ℕ := sorry

/-- Compute `(∑ k ∈ Finset.range 10, (k + 1)!) % 100`. -/
theorem c09_factorial_mod :
    (∑ k ∈ Finset.range 10, (k + 1).factorial) % 100 = c09_answer := by
  sorry
