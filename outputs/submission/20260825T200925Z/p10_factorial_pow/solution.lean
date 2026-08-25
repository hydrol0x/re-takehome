import Mathlib
import Mathlib.Tactic

open Nat

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

-- Helper lemmas -------------------------------------------------------------

/-- `6! < 3 ^ 6`. -/
lemma factorial_lt_pow_6 : Nat.factorial 6 < 3 ^ 6 := by
  norm_num

/-- For any `k`, `3 ^ (k + 7) ≤ (k + 7)!`. -/
lemma pow_le_fact_from_seven (k : ℕ) : 3 ^ (k + 7) ≤ Nat.factorial (k + 7) := by
  induction k with
  | zero =>
      norm_num
  | succ k ih =>
      have h3le : (3 : ℕ) ≤ k + 8 := by omega
      calc
        3 ^ (k + 7 + 1)
            = 3 ^ (k + 7) * 3 := by
              simpa [Nat.pow_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        _ ≤ Nat.factorial (k + 7) * 3 := by
              exact Nat.mul_le_mul_right _ ih
        _ ≤ Nat.factorial (k + 7) * (k + 8) := by
              exact Nat.mul_le_mul_left _ h3le
        _ = Nat.factorial (k + 8) := by
              simpa [Nat.factorial_succ, Nat.add_comm, Nat.add_left_comm,
                     Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

/-- For any `n ≥ 7`, `3 ^ n ≤ n!`. -/
lemma pow_le_fact_of_ge_seven (n : ℕ) (hn : 7 ≤ n) :
    3 ^ n ≤ Nat.factorial n := by
  rcases Nat.exists_eq_add_of_le hn with ⟨k, rfl⟩
  simpa [Nat.add_comm] using pow_le_fact_from_seven k

-- Main theorem --------------------------------------------------------------

/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  refine ⟨?mem, ?upper⟩
  · -- membership
    exact factorial_lt_pow_6
  · -- upper bound
    intro n hnmem
    by_contra hle
    have h7 : 7 ≤ n := by
      have hlt : 6 < n := Nat.lt_of_not_ge hle
      exact Nat.succ_le_of_lt hlt
    have hpow := pow_le_fact_of_ge_seven n h7
    have : Nat.factorial n < Nat.factorial n := lt_of_lt_of_le hnmem hpow
    exact (lt_irrefl _ this).elim
