import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  constructor
  · -- Show 6 ∈ S, i.e., 6! < 3^6
    norm_num [Nat.factorial]
  · -- Show ∀ m, m ∈ S → m ≤ 6
    intro m hm
    by_contra h
    -- If m > 6, then m ≥ 7
    have h_ge_7 : m ≥ 7 := by
      omega
    -- Prove by induction that for all n ≥ 7, n! ≥ 3^n
    have h_fact_ge_pow : ∀ k ≥ 7, Nat.factorial k ≥ 3 ^ k := by
      intro k hk
      induction' hk with k hk IH
      · -- Base case: k = 7
        norm_num [Nat.factorial]
      · -- Inductive step: assume for k, prove for k+1
        simp_all [Nat.factorial, pow_succ]
        nlinarith
    -- Apply this to m
    have h_m_fact_ge_pow : Nat.factorial m ≥ 3 ^ m := h_fact_ge_pow m h_ge_7
    -- But we also have m! < 3^m from hm
    linarith [hm]
