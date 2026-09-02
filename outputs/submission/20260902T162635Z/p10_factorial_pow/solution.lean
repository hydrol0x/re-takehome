import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

lemma six_in_set : Nat.factorial 6 < 3 ^ 6 := by norm_num

lemma seven_not_in_set : ¬(Nat.factorial 7 < 3 ^ 7) := by norm_num

lemma factorial_ge_pow_for_all_n_ge_7 : ∀ n : ℕ, n ≥ 7 → Nat.factorial n ≥ 3 ^ n := by
  intro n hn
  have h : Nat.factorial n ≥ 3 ^ n := by sorry
  exact h

theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by sorry
