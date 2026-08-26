import Mathlib

/-- The largest `k` such that `3 ^ k ∣ 100!`. Must be a numeric literal. -/
abbrev h01_answer : ℕ := 48

/-- `h01_answer` is the greatest `k` with `3 ^ k` dividing `100!`. -/
theorem h01_legendre100 :
    IsGreatest {k : ℕ | 3 ^ k ∣ Nat.factorial 100} h01_answer := by
  constructor
  · -- Prove that 3^48 divides 100!
    norm_num [Nat.dvd_factorial]
    <;> decide
  
  · -- Prove that for any k, if 3^k divides 100!, then k ≤ 48
    intro k hk
    have h₁ : ¬(3 ^ 49 ∣ Nat.factorial 100) := by
      norm_num [Nat.dvd_factorial]
      <;> decide
    have h₂ : k ≤ 48 := by
      by_contra h
      push_neg at h
      have : 3 ^ k ∣ Nat.factorial 100 := hk
      have : k ≥ 49 := by omega
      have : 3 ^ 49 ∣ 3 ^ k := by
        apply pow_dvd_pow _
        omega
      have : 3 ^ 49 ∣ Nat.factorial 100 := dvd_trans this hk
      contradiction
    omega
