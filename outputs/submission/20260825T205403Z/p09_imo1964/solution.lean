import Mathlib

/-- For any k : ℕ, 2^(3*k) ≡ 1 (mod 7). -/
lemma two_pow_three_mul_mod_seven (k : ℕ) : 2 ^ (3 * k) % 7 = 1 := by induction k with
  | zero => norm_num
  | succ k ih =>
      rw [Nat.mul_succ, pow_add, Nat.mul_mod, ih]
      norm_num

/-- For any k : ℕ, 2^(3*k+1) ≡ 2 (mod 7). -/
lemma two_pow_three_mul_add_one_mod_seven (k : ℕ) : 2 ^ (3 * k + 1) % 7 = 2 := by sorry

/-- For any k : ℕ, 2^(3*k+2) ≡ 4 (mod 7). -/
lemma two_pow_three_mul_add_two_mod_seven (k : ℕ) : 2 ^ (3 * k + 2) % 7 = 4 := by sorry

/-- For any n > 0, if 3 ∣ n then 7 ∣ 2^n - 1. -/
lemma div_by_three_implies_div_by_seven (n : ℕ) (hn : 0 < n) (h : 3 ∣ n) : 7 ∣ 2 ^ n - 1 := by sorry

/-- For any n > 0, if 7 ∣ 2^n - 1 then 3 ∣ n. -/
lemma div_by_seven_implies_div_by_three (n : ℕ) (hn : 0 < n) (h : 7 ∣ 2 ^ n - 1) : 3 ∣ n := by sorry

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by sorry

/-- For any n > 0, 2^n + 1 is never divisible by 7. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by sorry
