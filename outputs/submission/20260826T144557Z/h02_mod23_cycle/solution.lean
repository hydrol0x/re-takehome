import Mathlib

set_option maxHeartbeats 1000000
set_option exponentiation.threshold 10000
set_option maxRecDepth 8000

/-- Core computation: 2^11 ≡ 1 (mod 23) -/
lemma two_pow_11_mod_23 : (2 ^ 11) % 23 = 1 := by norm_num

/-- Powers 1 through 10 are not congruent to 1 mod 23 -/
lemma two_pow_lt_11_neq_one {k : ℕ} (hpos : 0 < k) (hlt : k < 11) : (2 ^ k) % 23 ≠ 1 := by
  revert k hpos hlt
  intro k hpos hlt
  interval_cases k <;> norm_num

/-- Key lemma: 2^n ≡ 1 (mod 23) iff 11 | n -/
lemma two_pow_mod_order_iff {n : ℕ} : (2 ^ n) % 23 = 1 ↔ 11 ∣ n := by sorry

/-- Helper for part (b): 2^n ≡ -1 (mod 23) implies 2^(2n) ≡ 1 (mod 23) -/
lemma two_pow_neg_one_implies_double_pow_one {n : ℕ} : (2 ^ n) % 23 = 22 → (2 ^ (2 * n)) % 23 = 1 := by sorry

/-- Helper for part (b): if 11 | n then 2^n ≡ 1 (mod 23) -/
lemma eleven_dvd_implies_two_pow_one {n : ℕ} : 11 ∣ n → (2 ^ n) % 23 = 1 := by sorry

/-- Main theorem (a): 23 | 2^n - 1 iff 11 | n -/
theorem h02_a (n : ℕ) (hn : 0 < n) : 23 ∣ 2 ^ n - 1 ↔ 11 ∣ n := by sorry

/-- Main theorem (b): no positive n has 23 | 2^n + 1 -/
theorem h02_b (n : ℕ) (hn : 0 < n) : ¬23 ∣ 2 ^ n + 1 := by sorry
