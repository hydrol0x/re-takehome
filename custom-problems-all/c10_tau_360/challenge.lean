import Mathlib

/-- The number of positive divisors of `360`. Must be a numeric literal. -/
abbrev c10_answer : ℕ := sorry

/-- `360` has exactly `c10_answer` positive divisors. -/
theorem c10_tau_360 : (Nat.divisors 360).card = c10_answer := by
  sorry
