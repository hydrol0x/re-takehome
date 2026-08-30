import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  constructor
  · -- Show 6 ∈ S, i.e., 6! < 3^6
    norm_num [Nat.factorial]
  · -- Show ∀ n, n! < 3^n → n ≤ 6
    intro n hn
    by_contra h
    push_neg at h
    have h_ge_7 : 7 ≤ n := by omega
    
    -- Prove by induction that for all k ≥ 7, k! ≥ 3^k
    have h_main : ∀ k : ℕ, 7 ≤ k → Nat.factorial k ≥ 3 ^ k := by
      intro k hk
      induction' hk with k hk IH
      · -- Base case: k = 7
        norm_num [Nat.factorial]
      · -- Inductive step: assume for k, prove for k+1
        simp_all [Nat.factorial, pow_succ]
        nlinarith [pow_pos (by norm_num : (0 : ℕ) < 3) k]
    
    -- Apply the main lemma to get contradiction
    have h_fact_ge : Nat.factorial n ≥ 3 ^ n := h_main n h_ge_7
    linarith
