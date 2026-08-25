import Mathlib

/-- The largest `k` such that `3 ^ k ∣ 100!`. Must be a numeric literal. -/
abbrev h01_answer : ℕ := 48

/-- Helper lemma: 3^48 divides 100! using Legendre's formula calculation -/
lemma three_pow_divides_100_factorial : 3 ^ 48 ∣ Nat.factorial 100 := by
  -- Calculate the exponent of 3 in 100! using Legendre's formula:
  -- floor(100/3) + floor(100/9) + floor(100/27) + floor(100/81) = 33 + 11 + 3 + 1 = 48
  -- We verify this directly with computation
  norm_num [Nat.dvd_iff_mod_eq_zero, Nat.factorial]
  <;> decide

/-- Helper lemma: 3^(48+1) does NOT divide 100! -/
lemma three_pow_succ_not_divides_100_factorial : ¬(3 ^ 49 ∣ Nat.factorial 100) := by
  -- The exponent of 3 in 100! is exactly 48, so 3^49 cannot divide 100!
  norm_num [Nat.dvd_iff_mod_eq_zero, Nat.factorial] at *
  <;> decide

/-- Main theorem: h01_answer is the greatest k such that 3^k divides 100! -/
theorem h01_legendre100 :
    IsGreatest {k : ℕ | 3 ^ k ∣ Nat.factorial 100} h01_answer := by
  refine' ⟨_, _⟩
  · -- First part: h01_answer ∈ {k : ℕ | 3 ^ k ∣ Nat.factorial 100}
    rw [h01_answer]
    exact three_pow_divides_100_factorial
  · -- Second part: ∀ k ∈ {k : ℕ | 3 ^ k ∣ Nat.factorial 100}, k ≤ h01_answer
    intro k hk
    rw [h01_answer]
    by_contra h
    -- If k > 48, then 3^k does not divide 100!, contradiction
    have : 49 ≤ k := by omega
    have : 3 ^ k ∣ Nat.factorial 100 := hk
    have : ¬(3 ^ 49 ∣ Nat.factorial 100) := three_pow_succ_not_divides_100_factorial
    -- Since 49 ≤ k, we have 3^49 ∣ 3^k, so if 3^k ∣ 100!, then 3^49 ∣ 100!
    have : 3 ^ 49 ∣ 3 ^ k := by
      apply pow_dvd_pow
      omega
    have : 3 ^ 49 ∣ Nat.factorial 100 := dvd_trans this hk
    contradiction
