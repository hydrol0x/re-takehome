import Mathlib

-- Increase heartbeats/recursion depth for heavy computation
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

/-- The largest `k` such that `3 ^ k ∣ 100!`. Must be a numeric literal. -/
abbrev h01_answer : ℕ := 48

/-- Helper: Sum of floor divisions equals 48. -/
lemma legendre_sum_computation : 
    (∑ i ∈ Finset.range 4, 100 / 3 ^ (i + 1)) = 48 := by
  norm_num [Finset.sum_range_succ]

/-- Helper: 3^48 divides 100! -/
lemma dvd_power_of_three_48 : 3 ^ 48 ∣ Nat.factorial 100 := by norm_num

/-- Helper: 3^49 does not divide 100! -/
lemma not_dvd_power_of_three_49 : ¬(3 ^ 49 ∣ Nat.factorial 100) := by norm_num

/-- Main lemma: h01_answer is in the set -/
lemma answer_in_set : 3 ^ h01_answer ∣ Nat.factorial 100 := by
  rw [h01_answer]
  exact dvd_power_of_three_48

/-- `h01_answer` is the greatest `k` with `3 ^ k` dividing `100!`. -/
theorem h01_legendre100 :
    IsGreatest {k : ℕ | 3 ^ k ∣ Nat.factorial 100} h01_answer := by
  constructor
  · -- Membership: h01_answer ∈ {k | 3^k ∣ 100!}
    exact answer_in_set
  · -- Upper bound: ∀ k, 3^k ∣ 100! → k ≤ h01_answer
    intro k hk
    by_contra h
    push_neg at h
    -- h : h01_answer < k
    have h_ge_49 : k ≥ 49 := by
      rw [h01_answer] at h
      omega
    -- 3^49 divides 3^k because 49 ≤ k
    have dvd_pow : 3 ^ 49 ∣ 3 ^ k := pow_dvd_pow _ h_ge_49
    -- Transitivity: 3^49 divides 100!
    have dvd_fact : 3 ^ 49 ∣ Nat.factorial 100 := dvd_trans dvd_pow hk
    -- Contradiction with helper
    exact not_dvd_power_of_three_49 dvd_fact
