import Mathlib

set_option maxHeartbeats 1000000
set_option exponentiation.threshold 10000
set_option maxRecDepth 8000

/-- Helper: Reduces power of 2 modulo 7 by reducing exponent modulo 3 -/
lemma pow_two_mod_7_periodic (n : ℕ) : (2 ^ n) % 7 = (2 ^ (n % 3)) % 7 := by calc
  (2 ^ n) % 7 = (2 ^ (3 * (n / 3) + n % 3)) % 7 := by
    rw [Nat.div_add_mod n 3]
    <;> ring_nf
  _ = (2 ^ (n % 3)) % 7 := by
    have h : 2 ^ 3 % 7 = 1 := by norm_num
    rw [pow_add, pow_mul]
    simp [Nat.pow_mod, Nat.mul_mod, h]
    <;> induction (n / 3) <;> simp [*, pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod] at * <;>
      norm_num at * <;> omega

/-- Helper: Computes 2^r mod 7 for r < 3 -/
lemma pow_two_mod_7_base_cases (r : ℕ) (hr : r < 3) : (2 ^ r) % 7 = if r = 0 then 1 else if r = 1 then 2 else 4 := by interval_cases r <;> norm_num [if_pos, if_neg]

/-- Helper: Relates divisibility of (2^n - 1) by 7 to 2^n mod 7 -/
lemma div_7_sub_1_iff (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ (2 ^ n) % 7 = 1 := by sorry

/-- Helper: Relates divisibility of (2^n + 1) by 7 to 2^n mod 7 -/
lemma div_7_add_1_iff (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n + 1 ↔ (2 ^ n) % 7 = 6 := by omega

/-- Main theorem (a): 7 divides 2^n - 1 iff 3 divides n -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  sorry

/-- Main theorem (b): 7 does not divide 2^n + 1 for positive n -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  sorry
