import Mathlib

/-- The largest `k` such that `3 ^ k ∣ 100!`. Must be a numeric literal. -/
abbrev h01_answer : ℕ := 48

/-- Helper: 3 is prime -/
lemma three_is_prime : Nat.Prime 3 := by norm_num

/-- Helper: Log computation for base 3, argument 100 -/
lemma log_three_hundred : Nat.log 3 100 = 4 := by norm_num

/-- Helper: Individual terms in Legendre sum -/
lemma legendre_term_0 : 100 / 3 ^ 1 = 33 := by norm_num
lemma legendre_term_1 : 100 / 3 ^ 2 = 11 := by norm_num
lemma legendre_term_2 : 100 / 3 ^ 3 = 3 := by norm_num
lemma legendre_term_3 : 100 / 3 ^ 4 = 1 := by norm_num
lemma legendre_term_4 : 100 / 3 ^ 5 = 0 := by norm_num

/-- Helper: Sum of Legendre terms equals 48 -/
lemma legendre_sum_eq_48 : 
    ∑ i ∈ Finset.range 5, 100 / 3 ^ (i + 1) = 48 := by norm_num

/-- Helper: General divisibility via Legendre's formula -/
lemma legendre_formula_divides :
    ∀ p n, Nat.Prime p →
      p ^ (∑ i ∈ Finset.range (Nat.log p n + 1), n / p ^ (i + 1)) ∣ n.factorial := by sorry

/-- Main divisibility fact: 3^48 divides 100! -/
lemma three_pow_48_divides_factorial :
    3 ^ h01_answer ∣ Nat.factorial 100 := by norm_num

/-- Upper bound: for any k > 48, 3^k does not divide 100! -/
lemma upper_bound_property :
    ∀ k : ℕ, k > h01_answer → ¬(3 ^ k ∣ Nat.factorial 100) := by sorry

/-- Theorem: h01_answer is the greatest k with 3^k dividing 100! -/
theorem h01_legendre100 :
    IsGreatest {k : ℕ | 3 ^ k ∣ Nat.factorial 100} h01_answer := by -- Proof 1: Direct construction using IsGreatest definition
    refine' ⟨_, _⟩
    · -- Show 48 is in the set: 3^48 ∣ 100!
      exact three_pow_48_divides_factorial
    · -- Show 48 is an upper bound
      intro k hk
      by_contra h
      have : k > h01_answer := by omega
      have : ¬(3 ^ k ∣ Nat.factorial 100) := upper_bound_property k this
      contradiction
