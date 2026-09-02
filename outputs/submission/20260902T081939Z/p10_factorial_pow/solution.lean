import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  have h_member : Nat.factorial 6 < 3 ^ 6 := by norm_num [Nat.factorial]
  
  have h_upper_bound : ∀ n, Nat.factorial n < 3 ^ n → n ≤ 6 := by
    intro n hn
    by_contra h
    -- Assume n ≥ 7 and derive contradiction
    have h' : n ≥ 7 := by omega
    
    -- Show that for all n ≥ 7, n! ≥ 3^n
    have h_fact_ge_pow : ∀ k ≥ 7, Nat.factorial k ≥ 3 ^ k := by
      intro k hk
      induction' hk with k hk IH
      · -- Base case: k = 7
        norm_num [Nat.factorial]
      · -- Inductive step: assume for k, prove for k+1
        simp_all [Nat.factorial, pow_succ]
        nlinarith [pow_pos (by norm_num : (0 : ℕ) < 3) k]
    
    specialize h_fact_ge_pow n h'
    linarith
  
  refine ⟨h_member, fun n hn => ?_⟩
  exact h_upper_bound n hn
