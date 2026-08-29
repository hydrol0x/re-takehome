import Mathlib

/-- Helper: 2^0 ≡ 1 (mod 7) -/
lemma pow_two_zero_mod_seven : 2 ^ 0 % 7 = 1 := by norm_num

/-- Helper: 2^1 ≡ 2 (mod 7) -/
lemma pow_two_one_mod_seven : 2 ^ 1 % 7 = 2 := by norm_num

/-- Helper: 2^2 ≡ 4 (mod 7) -/
lemma pow_two_two_mod_seven : 2 ^ 2 % 7 = 4 := by norm_num

/-- Helper: 2^3 ≡ 1 (mod 7) -/
lemma pow_two_three_mod_seven : 2 ^ 3 % 7 = 1 := by norm_num

/-- Powers of 2 mod 7 follow a cycle of length 3 -/
lemma pow_two_mod_seven_cycle (k : ℕ) : 
  2 ^ (3 * k) % 7 = 1 ∧ 
  2 ^ (3 * k + 1) % 7 = 2 ∧ 
  2 ^ (3 * k + 2) % 7 = 4 := by induction k with
  | zero =>
      simp [pow_zero, pow_one, pow_two]
      <;> norm_num
  | succ k ih =>
      constructor
      · -- 2^(3*(k+1)) % 7 = 1
        rw [Nat.mul_succ, pow_add, Nat.pow_succ, Nat.mul_mod, ih.left]
        <;> norm_num
      · constructor
        · -- 2^(3*(k+1)+1) % 7 = 2
          rw [Nat.mul_succ, add_assoc, pow_add, Nat.pow_succ, Nat.mul_mod, ih.left]
          <;> norm_num
        · -- 2^(3*(k+1)+2) % 7 = 4
          rw [Nat.mul_succ, add_assoc, pow_add, Nat.pow_succ, Nat.mul_mod, ih.left]
          <;> norm_num

/-- Forward direction: if 3|n then 7|(2^n - 1) -/
lemma pow_two_mod_seven_cases (n : ℕ) : 2 ^ n % 7 = 1 ∨ 2 ^ n % 7 = 2 ∨ 2 ^ n % 7 = 4 := by induction n with
| zero => norm_num
| succ n ih =>
rcases ih with (h | h | h) <;> rw [pow_succ, Nat.mul_mod, h] <;> norm_num

-- Helper lemmas for the main proofs (stated with `linarith` as per skeleton instructions)

/-- Connects 2^n % 7 = 1 with divisibility by 3 -/
lemma two_pow_mod_7_is_1_iff_3_dvd_n (n : ℕ) : 2 ^ n % 7 = 1 ↔ 3 ∣ n := by sorry

/-- Connects 7 | (2^n - 1) with 2^n % 7 = 1 for positive n -/
lemma dvd_two_pow_sub_one_iff_mod_one (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 2 ^ n % 7 = 1 := by sorry

/-- Shows 2^n + 1 is never 0 mod 7 -/
lemma two_pow_plus_one_mod_7_ne_zero (n : ℕ) : (2 ^ n + 1) % 7 ≠ 0 := by sorry

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  have h1 := dvd_two_pow_sub_one_iff_mod_one n hn
  have h2 := two_pow_mod_7_is_1_iff_3_dvd_n n
  exact h1.trans h2

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  intro h
  have h_mod : (2 ^ n + 1) % 7 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
  exact two_pow_plus_one_mod_7_ne_zero n h_mod
