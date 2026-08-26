import Mathlib

/-!
# h02_mod23_cycle

Proof skeleton for showing the order of 2 modulo 23 is 11.
-/

-- Compute 2^11 mod 23
lemma h02_pow_11_mod_23 : 2 ^ 11 % 23 = 1 := by
  norm_num

-- Check that 2^k ≠ 1 (mod 23) for 0 < k < 11
lemma h02_pow_lt_11_ne_1 {k : ℕ} (hk_pos : 0 < k) (hk_lt : k < 11) : 2 ^ k % 23 ≠ 1 := by
  interval_cases k <;> norm_num

-- Check that 2^k ≠ 22 (mod 23) for 0 < k ≤ 11  
lemma h02_pow_le_11_ne_22 {k : ℕ} (hk_pos : 0 < k) (hk_le : k ≤ 11) : 2 ^ k % 23 ≠ 22 := by
  interval_cases k <;> norm_num

-- If 2^n ≡ 1 (mod 23) and n > 0, then 11 | n
lemma h02_order_11_imp_div {n : ℕ} (hn_pos : 0 < n) (h_mod : 2 ^ n % 23 = 1) : 11 ∣ n := by sorry

-- If 11 | n, then 2^n ≡ 1 (mod 23)
lemma h02_pow_multiple_11 {n : ℕ} (hdiv : 11 ∣ n) : 2 ^ n % 23 = 1 := by sorry

-- If 2^n ≡ 22 (mod 23) and n > 0, get contradiction
lemma h02_no_neg_one {n : ℕ} (hn_pos : 0 < n) (h_mod : 2 ^ n % 23 = 22) : False := by sorry

-- Main theorem (a)
theorem h02_a (n : ℕ) (hn : 0 < n) : 23 ∣ 2 ^ n - 1 ↔ 11 ∣ n := by sorry

-- Main theorem (b)
theorem h02_b (n : ℕ) (hn : 0 < n) : ¬23 ∣ 2 ^ n + 1 := by sorry
