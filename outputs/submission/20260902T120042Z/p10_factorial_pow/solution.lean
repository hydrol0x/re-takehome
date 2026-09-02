import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

lemma three_pow_le_factorial_of_ge7 (n : ℕ) (hn : 7 ≤ n) :
    3 ^ n ≤ Nat.factorial n := by
  have h_base : 3 ^ 7 ≤ Nat.factorial 7 := by norm_num
  induction' hn with n hn IH
  · exact h_base
  · have : n ≥ 7 := hn
    simp_all [Nat.factorial_succ, pow_succ]
    nlinarith [mul_self_nonneg (n - 6)]

/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  constructor
  · -- Show 6 is in the set: 6! < 3^6
    rw [p10_answer]
    norm_num [Nat.factorial]
  · -- Show every n in the set satisfies n ≤ 6
    intro n hn
    by_contra h
    -- h : ¬ n ≤ 6, which means 6 < n
    have hn_bound : 7 ≤ n := by
      simp only [p10_answer, Nat.not_le] at h
      omega
    -- Use the helper lemma to show 3^n ≤ n! for n ≥ 7
    have h_le : 3 ^ n ≤ Nat.factorial n := three_pow_le_factorial_of_ge7 n hn_bound
    -- This contradicts hn : n! < 3^n
    have h_contradiction : 3 ^ n < 3 ^ n := Nat.lt_of_le_of_lt h_le hn
    exact lt_irrefl _ h_contradiction
