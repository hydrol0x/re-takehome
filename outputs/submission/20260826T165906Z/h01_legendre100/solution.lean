import Mathlib

/-- The largest `k` such that `3 ^ k ∣ 100!`. Must be a numeric literal. -/
abbrev h01_answer : ℕ := 48

/-- `h01_answer` is the greatest `k` with `3 ^ k` dividing `100!`. -/
theorem h01_legendre100 :
    IsGreatest {k : ℕ | 3 ^ k ∣ Nat.factorial 100} h01_answer := by
  have h_main : 3 ^ 48 ∣ Nat.factorial 100 := by
    -- Verify 3^48 divides 100! by direct computation
    norm_num [Nat.dvd_iff_mod_eq_zero, Nat.factorial_succ]
    <;> decide
  
  have h_upper_bound : ∀ k : ℕ, 3 ^ k ∣ Nat.factorial 100 → k ≤ 48 := by
    intro k hk
    -- Use Legendre's formula: the exponent of 3 in 100! is floor(100/3) + floor(100/9) + floor(100/27) + floor(100/81) = 33 + 11 + 3 + 1 = 48
    -- If 3^k divides 100!, then k must be at most 48
    have h1 : 3 ^ 48 ∣ Nat.factorial 100 := h_main
    have h2 : ¬(3 ^ 49 ∣ Nat.factorial 100) := by
      -- Direct computation shows 3^49 does not divide 100!
      norm_num [Nat.dvd_iff_mod_eq_zero, Nat.factorial_succ]
      <;> decide
    
    -- Since 3^49 doesn't divide 100!, but 3^48 does, we know the maximum is 48
    by_contra h
    push_neg at h
    -- If k > 48, then k ≥ 49, so 3^k would be divisible by 3^49
    have h3 : k ≥ 49 := by omega
    have h4 : 3 ^ 49 ∣ 3 ^ k := by
      exact pow_dvd_pow _ (by omega)
    -- Since 3^49 divides 3^k and 3^k divides 100!, 3^49 would divide 100!
    have h5 : 3 ^ 49 ∣ Nat.factorial 100 := dvd_trans h4 hk
    contradiction
  
  constructor
  · -- Show 48 is in the set
    exact h_main
  · -- Show 48 is an upper bound
    intro k hk
    exact h_upper_bound k hk
