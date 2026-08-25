import Mathlib

/-- The largest `k` such that `3 ^ k ∣ 100!`. Must be a numeric literal. -/
abbrev h01_answer : ℕ := 48

/-- Helper: The sum in Legendre's formula for 3^k | 100! equals 48 -/
lemma legendre_sum_computation : 
  100 / 3 + 100 / 9 + 100 / 27 + 100 / 81 = 48 := by
  norm_num

/-- Helper: 3^48 divides 100! -/
lemma three_pow_48_divides_100_fact : 
  3 ^ 48 ∣ Nat.factorial 100 := by
  have h : 100 / 3 + 100 / 9 + 100 / 27 + 100 / 81 = 48 := legendre_sum_computation
  -- Use the fact that the sum of floor divisions gives the exact power
  rw [← h]
  apply Nat.dvd_of_mod_eq_zero
  norm_num [Nat.factorial_succ, Nat.mul_mod, Nat.pow_mod]
  <;> decide

/-- Helper: If 3^k divides 100!, then k ≤ 48 -/
lemma three_pow_k_divides_implies_k_le_48 :
  ∀ k : ℕ, 3 ^ k ∣ Nat.factorial 100 → k ≤ 48 := by
  intro k hk
  by_contra h
  push_neg at h
  have : k ≥ 49 := by omega
  have h₁ : 3 ^ 49 ∣ 3 ^ k := by
    apply pow_dvd_pow _
    omega
  have h₂ : 3 ^ 49 ∣ Nat.factorial 100 := dvd_trans h₁ hk
  have h₃ : ¬(3 ^ 49 ∣ Nat.factorial 100) := by
    norm_num [legendre_sum_computation]
    <;> decide
  exact h₃ h₂

/-- `h01_answer` is the greatest `k` with `3 ^ k` dividing `100!`. -/
theorem h01_legendre100 :
    IsGreatest {k : ℕ | 3 ^ k ∣ Nat.factorial 100} h01_answer := by
  constructor
  · -- Show h01_answer ∈ S (i.e., 3^48 ∣ 100!)
    exact three_pow_48_divides_100_fact
  · -- Show it's an upper bound
    intro k hk
    exact three_pow_k_divides_implies_k_le_48 k hk
