import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

lemma factorial_6_less_than_3_pow_6 : Nat.factorial 6 < 3 ^ 6 := by
  norm_num [Nat.factorial]

lemma factorial_ge_3_pow_for_n_ge_7 (n : ℕ) (h : n ≥ 7) : Nat.factorial n ≥ 3 ^ n := by
  sorry

lemma factorial_gt_3_pow_for_n_ge_7 (n : ℕ) (h : n ≥ 7) : ¬(Nat.factorial n < 3 ^ n) := by
  intro hlt
  linarith [factorial_ge_3_pow_for_n_ge_7 n h]

/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  constructor
  · -- Prove p10_answer ∈ S
    rw [p10_answer]
    exact factorial_6_less_than_3_pow_6
  · -- Prove p10_answer is an upper bound of S
    intro n hn
    by_cases h : n ≤ 6
    · -- Case n ≤ 6: already covered by membership check
      simp_all [p10_answer]
    · -- Case n > 6: i.e., n ≥ 7
      have h7 : n ≥ 7 := by omega
      have hnot : ¬(Nat.factorial n < 3 ^ n) := factorial_gt_3_pow_for_n_ge_7 n h7
      simp_all [p10_answer]
