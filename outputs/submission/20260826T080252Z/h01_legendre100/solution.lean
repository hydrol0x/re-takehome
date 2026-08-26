import Mathlib

/-- The largest `k` such that `3 ^ k ∣ 100!`. Must be a numeric literal. -/
abbrev h01_answer : ℕ := 48

/-- Legendre's formula: the exponent of prime p in n! equals sum of floor(n/p^i) for i≥1. -/
lemma legendre_formula_for_prime_in_factorial (p n : ℕ) [Fact (Nat.Prime p)] :
    Nat.factorization (Nat.factorial n) p = 
      (Finset.range (Nat.log p n + 1)).sum (fun i => n / p ^ (i + 1)) := by
  induction' n using Nat.strong_induction_on with n ih
  sorry

/-- The exact power of 3 dividing 100!. -/
lemma v3_of_100_factorial :
    Nat.factorization (Nat.factorial 100) 3 = 48 := by
  -- Candidate 1: Direct application of Legendre's formula with norm_num computation
  have h_sum : (Finset.range (Nat.log 3 100 + 1)).sum (fun i => 100 / 3 ^ (i + 1)) = 48 := by
    norm_num [Finset.sum_range_succ, Finset.sum_range_one, Nat.log, pow_succ]
  rw [legendre_formula_for_prime_in_factorial, h_sum]

/-- Helper: 3^48 divides 100! -/
lemma three_pow_48_divides_100_factorial :
    3 ^ 48 ∣ Nat.factorial 100 := by
  norm_num

/-- Helper: 3^49 does NOT divide 100! -/
lemma three_pow_49_not_divides_100_factorial :
    ¬(3 ^ 49 ∣ Nat.factorial 100) := by
  norm_num

/-- Main theorem: h01_answer is the greatest k with 3^k dividing 100! -/
theorem h01_legendre100 :
    IsGreatest {k : ℕ | 3 ^ k ∣ Nat.factorial 100} h01_answer := by
  rw [IsGreatest]
  constructor
  · exact three_pow_48_divides_100_factorial
  · intro k hk
    have : k ≤ 48 := by
      by_contra h
      have : k ≥ 49 := by omega
      have : 3 ^ 49 ∣ 3 ^ k := by
        exact Nat.pow_dvd_pow _ this
      have : 3 ^ 49 ∣ Nat.factorial 100 := dvd_trans this hk
      exact three_pow_49_not_divides_100_factorial this
    omega
