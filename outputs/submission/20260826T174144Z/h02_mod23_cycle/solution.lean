import Mathlib

/-- Compute 2^11 mod 23 equals 1 -/
lemma pow_2_11_mod_23 : 2 ^ 11 % 23 = 1 := by norm_num

/-- Powers of 2 mod 23 repeat with period 11 -/
lemma pow_2_cycle_mod_23 (k : ℕ) : 2 ^ k % 23 = 2 ^ (k % 11) % 23 := by sorry

/-- For positive n, 23 | 2^n - 1 implies 11 | n -/
lemma h02_a_forward (n : ℕ) (hn : 0 < n) (h : 23 ∣ 2 ^ n - 1) : 11 ∣ n := by sorry

/-- For positive n, 11 | n implies 23 | 2^n - 1 -/
lemma h02_a_backward (n : ℕ) (hn : 0 < n) (h : 11 ∣ n) : 23 ∣ 2 ^ n - 1 := by sorry

/-- No positive n satisfies 2^n ≡ -1 (mod 23) -/
lemma h02_b_helper (n : ℕ) (hn : 0 < n) : ¬(2 ^ n % 23 = 22) := by sorry

/-- (a): 23 ∣ 2 ^ n - 1 iff 11 ∣ n, for positive n. -/
theorem h02_a (n : ℕ) (hn : 0 < n) : 23 ∣ 2 ^ n - 1 ↔ 11 ∣ n := by
  constructor
  · exact h02_a_forward n hn
  · exact h02_a_backward n hn

/-- (b): no positive n has 23 ∣ 2 ^ n + 1. -/
theorem h02_b (n : ℕ) (hn : 0 < n) : ¬23 ∣ 2 ^ n + 1 := by
  intro h
  have h₁ : 2 ^ n % 23 = 22 := by omega
  exact h02_b_helper n hn h₁
