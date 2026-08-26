import Mathlib

set_option maxHeartbeats 1000000
set_option maxRecDepth 8000
set_option exponentiation.threshold 10000

/-- The last two digits of `3 ^ 2026`, i.e. `3 ^ 2026 % 100`. Must be a numeric literal. -/
abbrev c06_answer : ℕ := 29

/-- Compute `3 ^ 2026 % 100`. -/
theorem c06_three_pow : 3 ^ 2026 % 100 = c06_answer := by
  decide
