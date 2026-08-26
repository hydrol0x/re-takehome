import Mathlib

/-- The largest `k` such that `3 ^ k ∣ 100!`. Must be a numeric literal. -/
abbrev h01_answer : ℕ := 48

/-- `h01_answer` is the greatest `k` with `3 ^ k` dividing `100!`. -/
theorem h01_legendre100 :
    IsGreatest {k : ℕ | 3 ^ k ∣ Nat.factorial 100} h01_answer := by
  -- First, we need to prove that 3^48 divides 100!
  have h_mem : 3 ^ 48 ∣ Nat.factorial 100 := by
    norm_num [Nat.factorial, Nat.pow_succ]
    <;> decide
  
  -- Second, we need to prove that for any k > 48, 3^k does not divide 100!
  have h_upper_bound : ∀ k : ℕ, 3 ^ k ∣ Nat.factorial 100 → k ≤ 48 := by
    intro k hk
    -- Use the fact that the exponent of 3 in 100! is exactly 48
    -- Legendre's formula: v_3(100!) = ⌊100/3⌋ + ⌊100/9⌋ + ⌊100/27⌋ + ⌊100/81⌋ = 33 + 11 + 3 + 1 = 48
    have h : k ≤ 48 := by
      by_contra h'
      -- If k > 48, then 3^k would require more factors of 3 than are available in 100!
      have h'' : k ≥ 49 := by omega
      -- We know from Legendre's formula that 3^48 || 100! (exact divisibility)
      -- So 3^49 cannot divide 100!
      have h''' : ¬(3 ^ 49 ∣ Nat.factorial 100) := by
        norm_num [Nat.factorial, Nat.pow_succ] at *
        <;> 
        (try decide) <;>
        (try {
          -- The sum of exponents of 3 in 100! is exactly 48
          -- So 3^49 cannot divide 100!
          simp_all [Nat.dvd_factorial]
          <;> norm_num at *
          <;> omega
        })
      have h_k_ge_49 : 3 ^ k ∣ Nat.factorial 100 → 3 ^ 49 ∣ Nat.factorial 100 := by
        intro h_k_dvd
        have h_k_ge_49_exp : k ≥ 49 := h''
        have h_pow_dvd : 3 ^ 49 ∣ 3 ^ k := by
          apply pow_dvd_pow _
          omega
        exact dvd_trans h_pow_dvd h_k_dvd
      have h_final : False := by
        apply h'''
        exact h_k_ge_49 hk
      contradiction
    exact h
  
  -- Combine both parts to show 48 is the greatest element
  constructor
  · -- Prove 48 is in the set
    exact h_mem
  · -- Prove 48 is an upper bound
    intro k hk
    exact h_upper_bound k hk
