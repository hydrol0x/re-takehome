import Mathlib

/-- Helper: For any n, 2^n mod 7 depends only on n mod 3 -/
lemma pow_two_mod_seven_case_zero (k : ℕ) : 2 ^ (3 * k) % 7 = 1 := by induction k with
| zero => norm_num
| succ k ih =>
calc
  2 ^ (3 * (k + 1)) % 7
    = 2 ^ (3 * k + 3) % 7 := by rw [show 3 * (k + 1) = 3 * k + 3 by ring]
  _ = (2 ^ (3 * k) * 2 ^ 3) % 7 := by rw [pow_add]
  _ = ((2 ^ (3 * k) % 7) * (2 ^ 3 % 7)) % 7 := by rw [Nat.mul_mod]
  _ = (1 * (2 ^ 3 % 7)) % 7 := by rw [ih]
  _ = (1 * 1) % 7 := by rw [show 2 ^ 3 % 7 = 1 by norm_num]
  _ = 1 := by norm_num

/-- Helper: For any n, 2^n mod 7 depends only on n mod 3 -/
lemma pow_two_mod_seven_case_one (k : ℕ) : 2 ^ (3 * k + 1) % 7 = 2 := by induction k with
| zero => norm_num
| succ k ih =>
calc
  2 ^ (3 * (k + 1) + 1) % 7
    = 2 ^ (3 * k + 4) % 7 := by ring_nf
  _ = 2 ^ (3 * k + 1 + 3) % 7 := by rw [show 4 = 1 + 3 by norm_num]
  _ = (2 ^ (3 * k + 1) * 2 ^ 3) % 7 := by rw [pow_add]
  _ = ((2 ^ (3 * k + 1) % 7) * (2 ^ 3 % 7)) % 7 := by rw [Nat.mul_mod]
  _ = (2 * (2 ^ 3 % 7)) % 7 := by rw [ih]
  _ = (2 * 1) % 7 := by rw [show 2 ^ 3 % 7 = 1 by norm_num]
  _ = 2 := by norm_num

/-- Helper: For any n, 2^n mod 7 depends only on n mod 3 -/
lemma pow_two_mod_seven_case_two (k : ℕ) : 2 ^ (3 * k + 2) % 7 = 4 := by sorry

/-- Helper: Relates divisibility by 7 to modular arithmetic for 2^n - 1 -/
lemma div_seven_iff_mod_eq_zero (n : ℕ) : 7 ∣ 2 ^ n - 1 ↔ 2 ^ n % 7 = 1 := by sorry

/-- Main theorem p09_a: 7 | 2^n - 1 iff 3 | n for positive n -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by sorry

/-- Helper: 2^n mod 7 is never 6 for any n -/
lemma pow_two_mod_seven_never_six (n : ℕ) : 2 ^ n % 7 ≠ 6 := by sorry

/-- Main theorem p09_b: No positive n has 7 | 2^n + 1 -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by sorry
