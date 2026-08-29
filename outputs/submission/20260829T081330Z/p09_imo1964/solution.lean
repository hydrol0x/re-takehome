import Mathlib

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  rw [Nat.dvd_iff_mod_eq_zero]
  rw [← Nat.mod_add_div n 3]
  let k := n / 3
  let r := n % 3
  have h_r_lt : r < 3 := Nat.mod_lt _ (by decide)
  have h_n : n = 3 * k + r := by omega
  rw [h_n]
  sorry

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  intro h
  have h_rem : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h_rem with (h_rem | h_rem | h_rem)
  · have h_pow : 2 ^ n % 7 = 1 := by
      rw [← Nat.mod_add_div n 3]
      simp [h_rem, pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod]
    omega
  · have h_pow : 2 ^ n % 7 = 2 := by
      rw [← Nat.mod_add_div n 3]
      simp [h_rem, pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod]
    omega
  · have h_pow : 2 ^ n % 7 = 4 := by
      rw [← Nat.mod_add_div n 3]
      simp [h_rem, pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod]
    omega

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
  2 ^ (3 * k + 2) % 7 = 4 := by
  try intros
  simp [pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod]

/-- For any n, 2^n % 7 is one of {1, 2, 4} -/
lemma pow_two_mod_seven_cases (n : ℕ) : 2 ^ n % 7 = 1 ∨ 2 ^ n % 7 = 2 ∨ 2 ^ n % 7 = 4 := by
  induction n with
    | zero => norm_num
    | succ n ih =>
      rcases ih with (h | h | h) <;>
        simp [pow_succ, Nat.mul_mod, h] <;>
        norm_num

/-- If 3|n then 2^n ≡ 1 (mod 7) -/
lemma div_three_implies_pow_mod_one (n : ℕ) (h : 3 ∣ n) : 2 ^ n % 7 = 1 := by
  rcases h with ⟨k, hk⟩
  rw [hk]
  exact (pow_two_mod_seven_cycle k).1

/-- If 2^n ≡ 1 (mod 7) then 3|n -/
lemma pow_mod_one_implies_div_three (n : ℕ) (h : 2 ^ n % 7 = 1) : 3 ∣ n := by
  sorry

/-- 2^n % 7 is never 6 for any n -/
lemma pow_two_mod_never_six (n : ℕ) : 2 ^ n % 7 ≠ 6 := by
  rcases pow_two_mod_seven_cases n with h | h | h <;> simp_all

/-- If 7 | (2^n + 1) then 2^n ≡ 6 (mod 7) -/
lemma div_implies_mod_six (n : ℕ) (h : 7 ∣ 2 ^ n + 1) : 2 ^ n % 7 = 6 := by
  omega
