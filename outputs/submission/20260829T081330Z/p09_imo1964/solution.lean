import Mathlib

/-- Powers of 2 mod 7 repeat every 3 steps -/
lemma pow_two_mod_seven_period (n k : ℕ) :
    (2 ^ (3 * k + n)) % 7 = (2 ^ n) % 7 := by induction k with
      | zero => simp
      | succ k ih =>
        calc
          (2 ^ (3 * (k + 1) + n)) % 7 
            = (2 ^ (3 * k + n + 3)) % 7 := by ring_nf
          _ = (2 ^ (3 * k + n) * 2 ^ 3) % 7 := by rw [pow_add]
          _ = ((2 ^ (3 * k + n)) % 7 * (2 ^ 3 % 7)) % 7 := by simp [Nat.mul_mod]
          _ = ((2 ^ n % 7) * 1) % 7 := by rw [ih]; norm_num
          _ = (2 ^ n) % 7 := by simp

/-- Case when exponent is multiple of 3 -/
lemma pow_two_mod_seven_zero_case (k : ℕ) : (2 ^ (3 * k)) % 7 = 1 := by calc
  (2 ^ (3 * k)) % 7 
    = ((2 ^ 3) ^ k) % 7 := by rw [pow_mul]
  _ = (8 ^ k) % 7 := by norm_num
  _ = 1 := by
    have h : ∀ m : ℕ, (8 ^ m) % 7 = 1 := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        simp [Nat.pow_succ, Nat.mul_mod, ih]
        <;> norm_num
    exact h k

/-- Case when exponent ≡ 1 (mod 3) -/
lemma pow_two_mod_seven_one_case (k : ℕ) : (2 ^ (3 * k + 1)) % 7 = 2 := by induction k with
| zero => norm_num
| succ k ih =>
  calc
    (2 ^ (3 * (k + 1) + 1)) % 7 
      = (2 ^ (3 * k + 4)) % 7 := by ring_nf
    _ = (2 ^ (3 * k + 1 + 3)) % 7 := by ring_nf
    _ = (2 ^ (3 * k + 1) * 2 ^ 3) % 7 := by rw [pow_add]
    _ = ((2 ^ (3 * k + 1)) % 7 * (2 ^ 3 % 7)) % 7 := by simp [Nat.mul_mod]
    _ = (2 * 1) % 7 := by rw [ih]; norm_num
    _ = 2 := by norm_num

/-- Case when exponent ≡ 2 (mod 3) -/
lemma pow_two_mod_seven_two_case (k : ℕ) : (2 ^ (3 * k + 2)) % 7 = 4 := by induction k with
| zero => norm_num
| succ k ih =>
  calc
    (2 ^ (3 * (k + 1) + 2)) % 7 
      = (2 ^ (3 * k + 5)) % 7 := by ring_nf
    _ = (2 ^ (3 * k + 2 + 3)) % 7 := by ring_nf
    _ = (2 ^ (3 * k + 2) * 2 ^ 3) % 7 := by rw [pow_add]
    _ = ((2 ^ (3 * k + 2)) % 7 * (2 ^ 3 % 7)) % 7 := by simp [Nat.mul_mod]
    _ = (4 * 1) % 7 := by rw [ih]; norm_num
    _ = 4 := by norm_num

/-- If 2^n ≡ 1 (mod 7) then 7 divides 2^n - 1 -/
lemma dvd_of_pow_mod_eq_one (n : ℕ) (h : 2 ^ n % 7 = 1) : 7 ∣ 2 ^ n - 1 := by omega

/-- If 7 divides 2^n + 1 then 2^n ≡ 6 (mod 7) -/
lemma plus_one_dvd_implies_mod_six (n : ℕ) (h : 7 ∣ 2 ^ n + 1) : 2 ^ n % 7 = 6 := by omega

/-- 2^n mod 7 is never 6 for any natural number n -/
lemma pow_two_never_mod_six (n : ℕ) : 2 ^ n % 7 ≠ 6 := by sorry

/-- For n > 0, 2^n ≡ 1 (mod 7) iff 3 divides n -/
theorem part_a_equiv (n : ℕ) (hn : 0 < n) : (2 ^ n) % 7 = 1 ↔ 3 ∣ n := by sorry

/-- Main theorem for part (a): 7 | 2^n - 1 iff 3 | n -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by sorry

/-- Main theorem for part (b): no positive n has 7 | 2^n + 1 -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by sorry
