import Mathlib

/-- Helper: compute 2^n mod 7 based on n mod 3 -/
lemma pow_two_mod_seven_cases (n : ℕ) : 2 ^ n % 7 = 
  if n % 3 = 0 then 1 else if n % 3 = 1 then 2 else 4 := by induction n with
  | zero => simp
  | succ n ih =>
    have h : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases h with (h | h | h) <;>
    simp_all [pow_succ, Nat.mul_mod, Nat.pow_mod, Nat.add_mod]
    <;> norm_num

/-- Helper: 7 divides 2^n - 1 iff n % 3 = 0 -/
lemma div_two_pow_minus_one_iff_zero_mod_three (n : ℕ) : 7 ∣ 2 ^ n - 1 ↔ n % 3 = 0 := by induction n with
| zero => simp
| succ n ih =>
sorry

/-- Helper: 2^n % 7 ≠ 6 for any n -/
lemma two_pow_mod_seven_ne_six (n : ℕ) : 2 ^ n % 7 ≠ 6 := by sorry

/-- Helper: if n % 3 = 0 then 3 divides n -/
lemma zero_mod_three_implies_three_div (n : ℕ) : n % 3 = 0 → 3 ∣ n := by omega

/-- Helper: if 3 divides n then n % 3 = 0 -/
lemma three_div_implies_zero_mod_three (n : ℕ) : 3 ∣ n → n % 3 = 0 := by omega

/-- Main theorem (a): 7 ∣ 2^n - 1 iff 3 ∣ n for positive n -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by calc
  7 ∣ 2 ^ n - 1 ↔ n % 3 = 0 := by
    simpa using div_two_pow_minus_one_iff_zero_mod_three n
  _ ↔ 3 ∣ n := by
    constructor
    · intro h
      exact zero_mod_three_implies_three_div n h
    · intro h
      exact three_div_implies_zero_mod_three n h

/-- Main theorem (b): no positive n has 7 ∣ 2^n + 1 -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by sorry
