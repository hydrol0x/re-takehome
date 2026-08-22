import Mathlib

/-- Key bound: from 7 on, the factorial dominates 3^n. -/
lemma three_pow_le_factorial : ∀ n : ℕ, 7 ≤ n → 3 ^ n ≤ Nat.factorial n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => norm_num [Nat.factorial]
  | succ n hn ih =>
      rw [Nat.factorial_succ, pow_succ]
      calc 3 ^ n * 3 ≤ Nat.factorial n * 3 := Nat.mul_le_mul_right 3 ih
        _ ≤ Nat.factorial n * (n + 1) := Nat.mul_le_mul_left _ (by omega)
        _ = (n + 1) * Nat.factorial n := Nat.mul_comm _ _

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  constructor
  · show Nat.factorial 6 < 3 ^ 6
    norm_num [Nat.factorial]
  · intro n hn
    show n ≤ 6
    by_contra hgt
    push_neg at hgt
    have hb := three_pow_le_factorial n (by omega)
    have : Nat.factorial n < Nat.factorial n := lt_of_lt_of_le hn hb
    exact absurd this (lt_irrefl _)
