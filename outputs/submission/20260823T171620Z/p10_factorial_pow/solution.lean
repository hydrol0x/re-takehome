import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  have h_mem : Nat.factorial 6 < 3 ^ 6 := by
    norm_num [Nat.factorial]
  
  have h_upper_bound : ∀ n ≥ 7, Nat.factorial n ≥ 3 ^ n := by
    intro n hn
    have : ∀ k : ℕ, k ≥ 7 → Nat.factorial k ≥ 3 ^ k := by
      intro k hk
      induction' hk with k hk IH
      · -- Base case: k = 7
        norm_num [Nat.factorial]
      · -- Inductive step
        simp_all [Nat.factorial, pow_succ]
        nlinarith [pow_pos (by norm_num : 0 < 3) k, 
                   Nat.mul_le_mul_right (3 ^ k) (by omega : 3 ≤ k + 2)]
    exact this n hn
  
  constructor
  · -- Prove 6 is in the set
    exact h_mem
  · -- Prove 6 is an upper bound
    intro n hn
    by_cases h : n = 6
    · -- If n = 6, then n ≤ 6
      rw [h]
    · -- If n ≠ 6, since n is in the set we have n! < 3^n
      -- But if n ≥ 7, we have n! ≥ 3^n by h_upper_bound
      cases' lt_or_gt_of_ne h with hlt hgt
      · -- n < 6, so n ≤ 6
        linarith
      · -- n > 6, so n ≥ 7
        have h_ge_7 : n ≥ 7 := by omega
        have h_fact_ge : Nat.factorial n ≥ 3 ^ n := h_upper_bound n h_ge_7
        have h_fact_lt : Nat.factorial n < 3 ^ n := hn
        linarith
