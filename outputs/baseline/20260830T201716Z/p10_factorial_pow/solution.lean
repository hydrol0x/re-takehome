import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  constructor
  · -- Show 6 ∈ {n : ℕ | n ! < 3 ^ n}
    norm_num [Nat.factorial]
  · -- Show ∀ n, n ∈ {n : ℕ | n ! < 3 ^ n} → n ≤ 6
    intro n hn
    by_contra h
    push Not at h
    have h_ge_7 : n ≥ 7 := by omega
    -- Prove by induction that for all k ≥ 7, k! ≥ 3^k
    have h_ind : ∀ k ≥ 7, Nat.factorial k ≥ 3 ^ k := by
      intro k hk
      induction' hk with k hk IH
      · -- Base case: k = 7
        norm_num [Nat.factorial]
      · -- Inductive step
        simp_all [Nat.factorial, pow_succ]
        nlinarith
    have h_fact_ge : Nat.factorial n ≥ 3 ^ n := h_ind n h_ge_7
    linarith
