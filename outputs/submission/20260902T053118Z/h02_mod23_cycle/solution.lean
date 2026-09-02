import Mathlib

/-- Powers of 2 modulo 23 repeat with period 11 -/
lemma pow_2_mod_23_periodic (k : ℕ) :
  2 ^ k % 23 = 2 ^ (k % 11) % 23 := by sorry

/-- The order of 2 modulo 23 is 11: 2^11 ≡ 1 (mod 23) -/
lemma pow_2_mod_23_order (k : ℕ) :
  2 ^ (11 * k) % 23 = 1 := by induction k with
  | zero => simp
  | succ k ih =>
    calc
      2 ^ (11 * (k + 1)) % 23 = 2 ^ (11 * k + 11) % 23 := by ring_nf
      _ = (2 ^ (11 * k) * 2 ^ 11) % 23 := by rw [pow_add]
      _ = ((2 ^ (11 * k) % 23) * (2 ^ 11 % 23)) % 23 := by rw [Nat.mul_mod]
      _ = (1 * (2 ^ 11 % 23)) % 23 := by rw [ih]
      _ = 2 ^ 11 % 23 := by simp [Nat.mul_one]
      _ = 1 := by norm_num

/-- Powers of 2 mod 23 equal 1 exactly when the exponent is divisible by 11 -/
lemma pow_2_mod_23_eq_one_iff (n : ℕ) :
  2 ^ n % 23 = 1 ↔ 11 ∣ n := by sorry

/-- Powers of 2 mod 23 are never congruent to -1 (i.e., 22) -/
lemma pow_2_mod_23_neq_neg_one (n : ℕ) :
  2 ^ n % 23 ≠ 22 := by sorry

/-- Part (a): 23 divides 2^n - 1 iff 11 divides n, for positive n -/
theorem h02_a (n : ℕ) (hn : 0 < n) : 23 ∣ 2 ^ n - 1 ↔ 11 ∣ n := by sorry

/-- Part (b): No positive n has 23 dividing 2^n + 1 -/
theorem h02_b (n : ℕ) (hn : 0 < n) : ¬23 ∣ 2 ^ n + 1 := by sorry