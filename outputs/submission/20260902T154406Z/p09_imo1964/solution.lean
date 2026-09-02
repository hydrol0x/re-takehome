import Mathlib

/-- Helper: 2^n mod 7 depends on n mod 3 -/
lemma pow_two_mod_seven_cases (n : ℕ) : 
  2 ^ n % 7 = if n % 3 = 0 then 1 else if n % 3 = 1 then 2 else 4 := by sorry

/-- Helper: 2^n ≡ 1 (mod 7) iff n ≡ 0 (mod 3) -/
lemma div_two_pow_minus_one (n : ℕ) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by sorry

/-- Part (a): For positive n, 7 ∣ 2^n - 1 iff 3 ∣ n -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by exact?

/-- Helper: 2^n + 1 mod 7 is never 0 for any n -/
lemma sum_two_pow_plus_one_mod_seven_ne_zero (n : ℕ) : (2 ^ n + 1) % 7 ≠ 0 := by sorry

/-- Part (b): No positive n has 7 ∣ 2^n + 1 -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by sorry
