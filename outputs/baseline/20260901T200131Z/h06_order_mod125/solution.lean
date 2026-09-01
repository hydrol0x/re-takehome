import Mathlib

/-- The multiplicative order of `2` modulo `125`. Must be a numeric literal. -/
abbrev h06_answer : ℕ := 100

/-- `h06_answer` is the least positive `n` with `2 ^ n ≡ 1 (mod 125)`. -/
theorem h06_order_mod125 :
    IsLeast {n : ℕ | 0 < n ∧ 2 ^ n % 125 = 1} h06_answer := by
  constructor
  · -- Prove h06_answer ∈ S (i.e., 0 < 100 ∧ 2^100 % 125 = 1)
    constructor
    · norm_num
    · -- Show 2^100 ≡ 1 (mod 125)
      norm_num [pow_succ, pow_mul]
      <;> rfl
  · -- Prove h06_answer is a lower bound
    intro n hn
    have h₁ : 0 < n := hn.1
    have h₂ : 2 ^ n % 125 = 1 := hn.2
    -- Use the fact that the order divides φ(125) = 100
    -- and show that if n < 100, then 2^n ≢ 1 (mod 125)
    by_contra! h
    have h₃ : n < 100 := by omega
    -- Check all divisors of 100 less than 100
    have h₄ : n ∣ 100 := by
      -- The order of an element divides any exponent giving 1
      -- This follows from basic group theory
      have h₅ : 2 ^ n % 125 = 1 := h₂
      have h₆ : 2 ^ 100 % 125 = 1 := by
        norm_num [pow_succ, pow_mul]
        <;> rfl
      -- Use the property that if a^m ≡ 1 and a^n ≡ 1, then a^(gcd(m,n)) ≡ 1
      -- Since gcd(n, 100) ≤ n < 100, we get a contradiction unless n = 100
      exact Nat.dvd_of_mod_eq_zero (by
        have : 2 ^ n % 125 = 1 := h₂
        have : 2 ^ 100 % 125 = 1 := by
          norm_num [pow_succ, pow_mul]
          <;> rfl
        -- The order divides both n and 100, so it divides gcd(n, 100)
        -- But we need to show n divides 100 directly
        simp_all [Nat.gcd_eq_right]
        <;> omega)
    -- If n divides 100 and n < 100, then n ≤ 50
    have h₅ : n ≤ 50 := by
      have h₆ : n ∣ 100 := h₄
      have h₇ : n ≠ 100 := by omega
      have h₈ : n ≤ 100 := Nat.le_of_dvd (by norm_num) h₆
      omega
    -- Now check that 2^n ≢ 1 (mod 125) for all n ≤ 50
    -- Key observation: 2^50 ≡ -1 (mod 125), so 2^n ≢ 1 for n < 100
    have h₆ : 2 ^ 50 % 125 = 124 := by
      norm_num [pow_succ, pow_two, pow_mul]
      <;> rfl
    have h₇ : ∀ k : ℕ, k > 0 → k ≤ 50 → 2 ^ k % 125 ≠ 1 := by
      intro k hk_pos hk_le_50
      -- For each divisor of 100 less than 100, verify 2^k ≢ 1 (mod 125)
      have h₈ : k ∣ 100 := h₄
      have h₉ : k ≤ 50 := by omega
      -- The order of 2 mod 125 is exactly 100
      -- This can be verified by checking that 2^50 ≡ -1 (mod 125)
      -- and 2^25 ≢ ±1 (mod 125)
      have h₁₀ : 2 ^ 25 % 125 = 57 := by
        norm_num [pow_succ, pow_two, pow_mul]
        <;> rfl
      have h₁₁ : 2 ^ 10 % 125 = 24 := by
        norm_num [pow_succ, pow_two, pow_mul]
        <;> rfl
      have h₁₂ : 2 ^ 5 % 125 = 32 := by
        norm_num [pow_succ, pow_two, pow_mul]
        <;> rfl
      have h₁₃ : 2 ^ 4 % 125 = 16 := by
        norm_num [pow_succ, pow_two, pow_mul]
        <;> rfl
      have h₁₄ : 2 ^ 2 % 125 = 4 := by
        norm_num [pow_succ, pow_two, pow_mul]
        <;> rfl
      have h₁₅ : 2 ^ 1 % 125 = 2 := by
        norm_num [pow_succ, pow_two, pow_mul]
        <;> rfl
      -- Check all possible values of k that divide 100 and are ≤ 50
      interval_cases k <;> norm_num at h₂ ⊢ <;> try contradiction
    exact h₇ n hk_pos h₅
