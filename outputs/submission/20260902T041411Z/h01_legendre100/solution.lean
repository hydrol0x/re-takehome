import Mathlib

/-- The largest `k` such that `3 ^ k ∣ 100!`. Must be a numeric literal. -/
abbrev h01_answer : ℕ := 48

/-- `h01_answer` is the greatest `k` with `3 ^ k` dividing `100!`. -/
theorem h01_legendre100 :
    IsGreatest {k : ℕ | 3 ^ k ∣ Nat.factorial 100} h01_answer := by
  constructor
  · -- Prove that 3^48 divides 100!
    norm_num [Nat.factorial]
    <;> decide
  · -- Prove that for any k in the set, k ≤ 48
    intro k hk
    have h₁ : 3 ^ k ∣ Nat.factorial 100 := hk
    have h₂ : k ≤ 48 := by
      -- Since 3^48 || 100! (exactly divides), 3^(49) does not divide 100!
      have h₃ : ¬(3 ^ 49 ∣ Nat.factorial 100) := by
        norm_num [Nat.factorial]
        <;> decide
      -- If k > 48, then k ≥ 49, so 3^k would be divisible by 3^49
      by_contra h
      push_neg at h
      have h₄ : k ≥ 49 := by omega
      have h₅ : 3 ^ 49 ∣ 3 ^ k := by
        apply pow_dvd_pow _ (by omega)
      have h₆ : 3 ^ 49 ∣ Nat.factorial 100 := dvd_trans h₅ h₁
      exact h₃ h₆
    exact h₂
