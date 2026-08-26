import Mathlib

/-- The largest `k` such that `3 ^ k ∣ 100!`. Must be a numeric literal. -/
abbrev h01_answer : ℕ := 48

/-- Helper: Sum from Legendre formula for p=3, n=100 equals 48 -/
lemma legendre_sum_3_100 :
  100 / 3 + 100 / 9 + 100 / 27 + 100 / 81 = 48 := by
  norm_num [Nat.div_eq_of_lt]
  <;> rfl

/-- Helper: 3^48 divides 100! -/
lemma three_pow_48_divides_factorial_100 :
  3 ^ 48 ∣ Nat.factorial 100 := by
  norm_num

/-- Helper: 3^49 does not divide 100! -/
lemma three_pow_49_not_divides_factorial_100 :
  ¬(3 ^ 49 ∣ Nat.factorial 100) := by
  norm_num

/-- Main helper: If 3^k divides 100! and k ≥ 49, contradiction -/
lemma div_3pow_implies_k_le_48 {k : ℕ} (h : 3 ^ k ∣ Nat.factorial 100) :
    k ≤ 48 := by
  by_contra hk
  have hk' : k ≥ 49 := by omega
  have : 3 ^ 49 ∣ 3 ^ k := pow_dvd_pow _ hk'
  exact three_pow_49_not_divides_factorial_100 (dvd_trans this h)

/-- `h01_answer` is the greatest `k` with `3 ^ k` dividing `100!`. -/
theorem h01_legendre100 :
    IsGreatest {k : ℕ | 3 ^ k ∣ Nat.factorial 100} h01_answer := by
  constructor
  · -- Show h01_answer ∈ S (i.e., 3^48 ∣ 100!)
    rw [h01_answer]
    exact three_pow_48_divides_factorial_100
  · -- Show ∀ k ∈ S, k ≤ h01_answer
    intro k hk
    rw [Set.mem_setOf_eq] at hk
    exact div_3pow_implies_k_le_48 hk
