import Mathlib

/-- The last two digits of `3 ^ 2026`, i.e. `3 ^ 2026 % 100`. Must be a numeric literal. -/
abbrev c06_answer : ℕ := 29

/-- Compute `3 ^ 2026 % 100`. -/
theorem c06_three_pow : 3 ^ 2026 % 100 = c06_answer := by
  conv_lhs => rw [show 2026 = 20 * 101 + 6 from rfl]
  rw [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num [c06_answer]
