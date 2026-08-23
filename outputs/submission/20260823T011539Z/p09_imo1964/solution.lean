import Mathlib

set_option maxHeartbeats 1000000
set_option exponentiation.threshold 10000

/-- Helper: For any k ≥ 0, the three consecutive powers of 2 mod 7 -/
lemma pow2_mod_7_pattern (k : ℕ) : 
  (2 ^ (3 * k)) % 7 = 1 ∧ 
  (2 ^ (3 * k + 1)) % 7 = 2 ∧ 
  (2 ^ (3 * k + 2)) % 7 = 4 := by sorry

/-- For any n, 2^n mod 7 equals 1, 2, or 4 depending on n mod 3 -/
lemma pow2_mod_7_case (n : ℕ) : 
  (2 ^ n) % 7 = if n % 3 = 0 then 1 
                else if n % 3 = 1 then 2 
                else 4 := by sorry

/-- 7 divides 2^n - 1 iff 2^n ≡ 1 (mod 7) -/
lemma div_sub_one_iff (n : ℕ) : 
  7 ∣ 2 ^ n - 1 ↔ (2 ^ n) % 7 = 1 := by sorry

-- Main theorem (a)
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  have h1 : 7 ∣ 2 ^ n - 1 ↔ (2 ^ n) % 7 = 1 := by apply div_sub_one_iff
  have h2 : (2 ^ n) % 7 = if n % 3 = 0 then 1 
                            else if n % 3 = 1 then 2 
                            else 4 := by apply pow2_mod_7_case
  rw [h1, h2]
  split_ifs <;> simp_all [Nat.dvd_iff_mod_eq_zero]
  <;> omega

/-- 2^n + 1 is never divisible by 7 for any n -/
lemma sum_not_div_7 (n : ℕ) : ¬7 ∣ 2 ^ n + 1 := by
  intro h
  have h1 : (2 ^ n) % 7 = if n % 3 = 0 then 1 
                            else if n % 3 = 1 then 2 
                            else 4 := pow2_mod_7_case n
  have h2 : (2 ^ n + 1) % 7 = 0 := by
    have h3 : 7 ∣ 2 ^ n + 1 := h
    rw [Nat.dvd_iff_mod_eq_zero] at h3
    exact h3
  simp [Nat.add_mod, pow_two] at h1 h2
  split_ifs at h1 h2 <;> norm_num at h1 h2 <;> omega

-- Main theorem (b)
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  apply sum_not_div_7
