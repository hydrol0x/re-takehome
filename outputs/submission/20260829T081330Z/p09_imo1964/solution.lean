import Mathlib

set_option maxHeartbeats 1000000
set_option exponentiation.threshold 10000
set_option maxRecDepth 8000

/-- Helper: 2^0 ≡ 1 (mod 7) -/
lemma pow_two_zero_mod_seven : 2 ^ 0 % 7 = 1 := by norm_num

/-- Helper: 2^1 ≡ 2 (mod 7) -/
lemma pow_two_one_mod_seven : 2 ^ 1 % 7 = 2 := by norm_num

/-- Helper: 2^2 ≡ 4 (mod 7) -/
lemma pow_two_two_mod_seven : 2 ^ 2 % 7 = 4 := by norm_num

/-- Helper: 2^3 ≡ 1 (mod 7) -/
lemma pow_two_three_mod_seven : 2 ^ 3 % 7 = 1 := by norm_num

/-- Powers of 2 mod 7 follow a cycle of length 3 -/
lemma pow_two_mod_seven_cycle (k : ℕ) : 
  2 ^ (3 * k) % 7 = 1 ∧ 
  2 ^ (3 * k + 1) % 7 = 2 ∧ 
  2 ^ (3 * k + 2) % 7 = 4 := by induction k with
  | zero =>
      simp [pow_zero, pow_one, pow_two]
      <;> norm_num
  | succ k ih =>
      constructor
      · -- 2^(3*(k+1)) % 7 = 1
        rw [Nat.mul_succ, pow_add, Nat.pow_succ, Nat.mul_mod, ih.left]
        <;> norm_num
      · constructor
        · -- 2^(3*(k+1)+1) % 7 = 2
          rw [Nat.mul_succ, add_assoc, pow_add, Nat.pow_succ, Nat.mul_mod, ih.left]
          <;> norm_num
        · -- 2^(3*(k+1)+2) % 7 = 4
          rw [Nat.mul_succ, add_assoc, pow_add, Nat.pow_succ, Nat.mul_mod, ih.left]
          <;> norm_num

/-- Forward direction: if 3|n then 7|(2^n - 1) -/
lemma p09_a_forward (n : ℕ) (hn : 0 < n) (h : 3 ∣ n) : 7 ∣ 2 ^ n - 1 := by sorry

/-- Backward direction: if 7|(2^n - 1) then 3|n -/
lemma p09_a_backward (n : ℕ) (hn : 0 < n) (h : 7 ∣ 2 ^ n - 1) : 3 ∣ n := by sorry

/-- Case analysis: 2^n mod 7 can only be 1, 2, or 4 -/
lemma pow_two_mod_seven_cases (n : ℕ) : 2 ^ n % 7 = 1 ∨ 2 ^ n % 7 = 2 ∨ 2 ^ n % 7 = 4 := by induction n with
| zero => norm_num
| succ n ih =>
rcases ih with (h | h | h) <;> rw [pow_succ, Nat.mul_mod, h] <;> norm_num

/-- 2^n + 1 mod 7 can only be 2, 3, or 5 (never 0) -/
lemma pow_two_plus_one_mod_seven_ne_zero (n : ℕ) : (2 ^ n + 1) % 7 ≠ 0 := by sorry

/-- Main theorem (a): 7 | 2^n - 1 iff 3 | n -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by sorry

/-- Main theorem (b): no positive n has 7 | 2^n + 1 -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by sorry
