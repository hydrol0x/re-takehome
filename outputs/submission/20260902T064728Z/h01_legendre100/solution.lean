import Mathlib

/-- The largest `k` such that `3 ^ k ∣ 100!`. Must be a numeric literal. -/
abbrev h01_answer : ℕ := 48

/-- The sum in Legendre's formula for v_3(100!) equals 48. -/
lemma legendre_sum_helper : 
    (100 / 3) + (100 / 9) + (100 / 27) + (100 / 81) = 48 := by
  norm_num

/-- Helper: v_3(100!) = 48 using Legendre's formula -/
lemma three_pow_48_divides_fact_100 : 
    3 ^ 48 ∣ Nat.factorial 100 := by
  norm_num

/-- For any k > 48, 3^k does not divide 100! -/
lemma three_pow_gt_48_not_divides_fact_100 : 
    ∀ k : ℕ, k > 48 → ¬(3 ^ k ∣ Nat.factorial 100) := by sorry

/-- Main theorem: h01_answer is the greatest k with 3^k dividing 100! -/
theorem h01_legendre100 :
    IsGreatest {k : ℕ | 3 ^ k ∣ Nat.factorial 100} h01_answer := by
  -- Part 1: h01_answer ∈ S (i.e., 3^48 ∣ 100!)
  have h_in : h01_answer ∈ {k : ℕ | 3 ^ k ∣ Nat.factorial 100} := by norm_num
  
  -- Part 2: For all k ∈ S, k ≤ h01_answer
  have h_upper : ∀ k : ℕ, k ∈ {k : ℕ | 3 ^ k ∣ Nat.factorial 100} → k ≤ h01_answer := by sorry
  
  -- Combine parts to show IsGreatest
  exact ⟨h_in, h_upper⟩
