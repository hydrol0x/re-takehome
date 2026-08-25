import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

--------------------------------------------------------------------
-- Helper lemmas
--------------------------------------------------------------------

-- 6! < 3^6, proved by computation.
lemma factorial_6_lt_pow_3 : Nat.factorial 6 < 3 ^ 6 := by
  norm_num

-- For every k, 3^(7+k) ≤ (7+k)!.
lemma pow_le_factorial_from_seven (k : ℕ) :
    3 ^ (7 + k) ≤ Nat.factorial (7 + k) := by
  induction k with
  | zero =>
      norm_num
  | succ k ih =>
      -- rewrite the goal using succ
      have hpow : 3 ^ (7 + Nat.succ k) = 3 ^ (7 + k) * 3 := by
        simpa [Nat.pow_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using rfl
      have hfac :
          Nat.factorial (7 + Nat.succ k) = (7 + Nat.succ k) * Nat.factorial (7 + k) := by
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
          Nat.factorial_succ (7 + k)
      have h_three_le : (3 : ℕ) ≤ 7 + Nat.succ k := by
        omega
      -- multiply the induction hypothesis by 3
      have h1 : 3 ^ (7 + k) * 3 ≤ Nat.factorial (7 + k) * 3 :=
        Nat.mul_le_mul_right 3 ih
      -- replace the factor 3 on the right by a larger factor
      have h2 : Nat.factorial (7 + k) * 3 ≤ Nat.factorial (7 + k) * (7 + Nat.succ k) := by
        have := Nat.mul_le_mul_left (Nat.factorial (7 + k)) h_three_le
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this
      -- combine the inequalities and rewrite
      have : 3 ^ (7 + Nat.succ k) ≤ Nat.factorial (7 + Nat.succ k) := by
        simpa [hpow, hfac, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
          (le_trans h1 h2)
      exact this

-- From the previous lemma we get the statement for any n ≥ 7.
lemma pow_le_factorial_of_seven (n : ℕ) (h : 7 ≤ n) :
    3 ^ n ≤ Nat.factorial n := by
  rcases Nat.exists_eq_add_of_le h with ⟨k, rfl⟩
  simpa using pow_le_factorial_from_seven k

--------------------------------------------------------------------
-- Main theorem
--------------------------------------------------------------------

/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  refine ⟨?mem, ?upper⟩
  · -- membership: 6 satisfies the inequality
    simpa [p10_answer] using factorial_6_lt_pow_3
  · -- upper bound: any n with n! < 3^n must be ≤ 6
    intro n hn
    by_contra hnot
    have hlt : 6 < n := Nat.lt_of_not_ge hnot
    have hseven : (7 : ℕ) ≤ n := Nat.succ_le_of_lt hlt
    have hpowle : 3 ^ n ≤ Nat.factorial n :=
      pow_le_factorial_of_seven n hseven
    have hcontr : ¬ Nat.factorial n < 3 ^ n := not_lt.mpr hpowle
    exact hcontr hn
