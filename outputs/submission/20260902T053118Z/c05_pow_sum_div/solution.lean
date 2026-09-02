import Mathlib

set_option maxHeartbeats 1000000
set_option exponentiation.threshold 10000
set_option maxRecDepth 8000

/-- 2025 is odd -/
lemma two_thousand_twenty_five_is_odd : Odd 2025 := by decide

/-- 3 ≡ -2 (mod 5) -/
lemma three_equiv_neg_two_mod_five : (3 : ℤ) ≡ -2 [ZMOD 5] := by norm_num

/-- Raising to odd power: (-a)^n ≡ -a^n when n is odd -/
lemma three_pow_equiv_neg_two_pow_mod_five : (3 : ℤ) ^ 2025 ≡ -((2 : ℤ) ^ 2025) [ZMOD 5] := by
  calc
    (3 : ℤ) ^ 2025 ≡ (-2 : ℤ) ^ 2025 [ZMOD 5] := by
      simpa using (three_equiv_neg_two_mod_five.pow 2025)
    _ ≡ -((2 : ℤ) ^ 2025) [ZMOD 5] := by
      simpa using (odd_pow_neg_equiv (a := (2 : ℤ)) two_thousand_twenty_five_is_odd)

/-- Sum of powers is 0 mod 5 -/
lemma sum_powers_zero_mod_five : ((2 : ℤ) ^ 2025 + (3 : ℤ) ^ 2025) ≡ 0 [ZMOD 5] := by
  calc
    (2 : ℤ) ^ 2025 + (3 : ℤ) ^ 2025 ≡ (2 : ℤ) ^ 2025 + (-(2 : ℤ) ^ 2025) [ZMOD 5] := by
      gcongr
      exact three_pow_equiv_neg_two_pow_mod_five
    _ = 0 := by ring

/-- `5` divides `2 ^ 2025 + 3 ^ 2025`. -/
theorem c05_pow_sum_div : 5 ∣ 2 ^ 2025 + 3 ^ 2025 := by
  rw [← Int.ofNat_dvd]
  have h : ((2 : ℤ) ^ 2025 + (3 : ℤ) ^ 2025) % 5 = 0 := by
    rw [Int.emod_def]
    simp [sum_powers_zero_mod_five, Int.ModEq]
  omega
