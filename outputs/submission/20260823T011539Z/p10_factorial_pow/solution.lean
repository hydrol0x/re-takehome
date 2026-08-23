import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

/-- `p10_member` proves that 6 satisfies the factorial inequality. -/
lemma p10_member : Nat.factorial 6 < 3 ^ 6 := by norm_num

/-- For all n ≥ 7, n! ≥ 3^n (upper bound property) -/
lemma p10_upper_bound : ∀ n ≥ 7, Nat.factorial n ≥ 3 ^ n := by sorry

/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by sorry
