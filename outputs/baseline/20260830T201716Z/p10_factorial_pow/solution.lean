import Mathlib

/-- The largest natural `n` with `n ! < 3 ^ n`. Must be a numeric literal. -/
abbrev p10_answer : ℕ := 6

/-- `p10_answer` is the greatest element of `{n : ℕ | n ! < 3 ^ n}`. -/
theorem p10_factorial_pow :
    IsGreatest {n : ℕ | Nat.factorial n < 3 ^ n} p10_answer := by
  constructor
  · -- Show 6 ∈ S, i.e., 6! < 3^6
    norm_num [Nat.factorial]
  · -- Show ∀ n, n ∈ S → n ≤ 6
    intro n hn
    by_contra h
    have h' : n ≥ 7 := by omega
    have h_main : Nat.factorial n ≥ 3 ^ n := by
      have : ∀ k, k ≥ 7 → Nat.factorial k ≥ 3 ^ k := by
        intro k hk
        induction' hk with k hk IH
        · -- Base case: k = 7
          norm_num [Nat.factorial]
        · -- Inductive step: k+1
          simp [Nat.factorial, pow_succ] at *
          have : k + 1 ≥ 8 := by omega
          nlinarith
      exact this n h'
    -- Contradiction: n ∈ S means n! < 3^n, but we proved n! ≥ 3^n
    linarith
