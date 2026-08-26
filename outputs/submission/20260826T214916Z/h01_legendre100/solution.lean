import Mathlib

/-- The largest `k` such that `3 ^ k ∣ 100!`. Must be a numeric literal. -/
abbrev h01_answer : ℕ := 48

/-- Helper: Compute floor(100 / 3) = 33 -/
lemma floor_100_div_3 : (100 / 3 : ℕ) = 33 := by norm_num

/-- Helper: Compute floor(100 / 9) = 11 -/
lemma floor_100_div_9 : (100 / 9 : ℕ) = 11 := by norm_num

/-- Helper: Compute floor(100 / 27) = 3 -/
lemma floor_100_div_27 : (100 / 27 : ℕ) = 3 := by norm_num

/-- Helper: Compute floor(100 / 81) = 1 -/
lemma floor_100_div_81 : (100 / 81 : ℕ) = 1 := by norm_num

/-- Helper: Legendre's formula sum for p=3, n=100 -/
theorem legendre_sum_100_3 : 
    (100 / 3) + (100 / 9) + (100 / 27) + (100 / 81) = 48 := by
  norm_num [floor_100_div_3, floor_100_div_9, floor_100_div_27, floor_100_div_81]

/-- Helper: The valuation of 3 in 100! equals 48 via Legendre's formula -/
theorem val_3_in_factorial_100 : 
    Nat.factorization (Nat.factorial 100) 3 = 48 := by sorry

/-- Helper: If p^k divides n!, then k ≤ v_p(n!) -/
theorem div_le_val {p : ℕ} (hp : Nat.Prime p) {n k : ℕ} 
    (h : p ^ k ∣ Nat.factorial n) : k ≤ Nat.factorization (Nat.factorial n) p := by sorry

/-- Main theorem: h01_answer is the greatest k with 3^k dividing 100! -/
theorem h01_legendre100 :
    IsGreatest {k : ℕ | 3 ^ k ∣ Nat.factorial 100} h01_answer := by
  -- Step 1: Show 48 ∈ S (3^48 divides 100!)
  have h_in : 3 ^ h01_answer ∣ Nat.factorial 100 := by norm_num
  
  -- Step 2: Show 48 is an upper bound (for any k with 3^k | 100!, we have k ≤ 48)
  have h_upper : ∀ k, 3 ^ k ∣ Nat.factorial 100 → k ≤ h01_answer := by
    intro k hk
    have h_val : Nat.factorization (Nat.factorial 100) 3 = 48 := by exact?
    have h_le : k ≤ Nat.factorization (Nat.factorial 100) 3 := by
      have hp : Nat.Prime 3 := by decide
      exact div_le_val hp hk
    rw [h_val] at h_le
    exact h_le
  
  -- Combine both conditions for IsGreatest
  constructor
  · exact h_in
  · exact h_upper
