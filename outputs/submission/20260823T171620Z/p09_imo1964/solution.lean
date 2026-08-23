import Mathlib

set_option maxHeartbeats 1000000
set_option exponentiation.threshold 10000
set_option maxRecDepth 8000

/-- Helper: Periodicity of powers of 2 modulo 7 -/
lemma pow_two_mod_7_period (n : ℕ) : 2 ^ (n + 3) % 7 = 2 ^ n % 7 := by induction n with
| zero => norm_num
| succ n ih =>
    calc
      2 ^ ((n + 1) + 3) % 7 = 2 ^ (n + 4) % 7 := by ring_nf
      _ = (2 ^ 3 * 2 ^ (n + 1)) % 7 := by rw [← pow_add]; ring_nf
      _ = ((2 ^ 3 % 7) * (2 ^ (n + 1) % 7)) % 7 := by simp [Nat.mul_mod]
      _ = (1 * (2 ^ (n + 1) % 7)) % 7 := by norm_num
      _ = 2 ^ (n + 1) % 7 := by simp

/-- Helper: Case n % 3 = 0 implies 2^n ≡ 1 (mod 7) -/
lemma pow_two_mod_7_case_0 (n : ℕ) (h : n % 3 = 0) : 2 ^ n % 7 = 1 := by sorry

/-- Helper: Case n % 3 = 1 implies 2^n ≡ 2 (mod 7) -/
lemma pow_two_mod_7_case_1 (n : ℕ) (h : n % 3 = 1) : 2 ^ n % 7 = 2 := by sorry

/-- Helper: Case n % 3 = 2 implies 2^n ≡ 4 (mod 7) -/
lemma pow_two_mod_7_case_2 (n : ℕ) (h : n % 3 = 2) : 2 ^ n % 7 = 4 := by sorry

/-- Helper: Relates divisibility of (k - 1) by 7 to k % 7 = 1 -/
lemma mod_sub_one_iff (k : ℕ) (hk : 1 ≤ k) : (k - 1) % 7 = 0 ↔ k % 7 = 1 := by omega

/-- Helper: Reduces 7 ∣ 2^n - 1 to 2^n % 7 = 1 for positive n -/
lemma dvd_pow_two_minus_one_iff (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 2 ^ n % 7 = 1 := by sorry

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  sorry

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  sorry
