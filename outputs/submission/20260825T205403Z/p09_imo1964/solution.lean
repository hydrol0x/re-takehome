import Mathlib

/-- Powers of 2 mod 7 for multiples of 3 -/
lemma pow_two_mod_three_base : ∀ k : ℕ, 2 ^ (3 * k) % 7 = 1 := by
  intro k
  induction k with
  | zero =>
      simp
  | succ k ih =>
      calc
        2 ^ (3 * (k.succ)) % 7
            = (2 ^ (3 * k + 3)) % 7 := by
              simpa [Nat.mul_succ]
        _ = ((2 ^ (3 * k) * 2 ^ 3) % 7) := by
              simpa [pow_add]
        _ = ((2 ^ (3 * k) % 7) * (2 ^ 3 % 7)) % 7 := by
              simpa [Nat.mul_mod]
        _ = (1 * (2 ^ 3 % 7)) % 7 := by
              simpa [ih]
        _ = (2 ^ 3 % 7) % 7 := by simp
        _ = 1 := by norm_num

/-- Powers of 2 mod 7 for 3k+1 -/
lemma pow_two_mod_three_one : ∀ k : ℕ, 2 ^ (3 * k + 1) % 7 = 2 := by
  intro k
  induction k with
  | zero =>
      simp
  | succ k ih =>
      calc
        2 ^ (3 * (k.succ) + 1) % 7
            = (2 ^ (3 * k + 4)) % 7 := by
              simpa [Nat.mul_succ, add_assoc]
        _ = (2 ^ (3 * k + 1 + 3)) % 7 := by
              ring_nf
        _ = ((2 ^ (3 * k + 1) * 2 ^ 3) % 7) := by
              rw [pow_add]
        _ = ((2 ^ (3 * k + 1) % 7) * (2 ^ 3 % 7)) % 7 := by
              rw [Nat.mul_mod]
        _ = (2 * (2 ^ 3 % 7)) % 7 := by
              rw [ih]
        _ = (2 * 1) % 7 := by norm_num
        _ = 2 := by norm_num

/-- Powers of 2 mod 7 for 3k+2 -/
lemma pow_two_mod_three_two : ∀ k : ℕ, 2 ^ (3 * k + 2) % 7 = 4 := by
  intro k
  calc
    2 ^ (3 * k + 2) % 7
        = (2 ^ (3 * k) * 2 ^ 2) % 7 := by
          rw [pow_add]
    _ = ((2 ^ (3 * k) % 7) * (2 ^ 2 % 7)) % 7 := by
          rw [Nat.mul_mod]
    _ = (1 * 4) % 7 := by
          rw [pow_two_mod_three_base]
          <;> norm_num
    _ = 4 := by norm_num

/-- Characterization of divisibility by 3 -/
lemma three_dvd_iff_mod_zero : ∀ n : ℕ, 3 ∣ n ↔ n % 3 = 0 := by
  omega

/-- If n is not divisible by 3, then n%3 ≠ 0 -/
lemma not_dvd_implies_mod_neq_zero : ∀ n : ℕ, ¬(3 ∣ n) → n % 3 ≠ 0 := by
  omega

/-- If n%3 = 0, then 3 divides n -/
lemma mod_zero_implies_dvd : ∀ n : ℕ, n % 3 = 0 → 3 ∣ n := by
  omega

/-- Remainder of 2^n when divided by 7 depends on n mod 3 -/
lemma pow_two_mod_seven_by_rem : ∀ n : ℕ, 2 ^ n % 7 = 
  if n % 3 = 0 then 1
  else if n % 3 = 1 then 2
  else 4 := by
  sorry

/-- For positive n, 2^n ≥ 1 -/
lemma two_pow_pos_ge_one : ∀ n : ℕ, 0 < n → 1 ≤ 2 ^ n := by
  exact?

/-- Main theorem (a): 7 divides 2^n - 1 iff 3 divides n -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  sorry

/-- Main theorem (b): no positive n has 7 dividing 2^n + 1 -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  by_contra H
  rw [Nat.dvd_iff_mod_eq_zero] at H
  have h : 2 ^ n % 7 = 1 ∨ 2 ^ n % 7 = 2 ∨ 2 ^ n % 7 = 4 := by
    have := pow_two_mod_seven_by_rem n
    split_ifs at this <;> simp_all
    <;> omega
  rcases h with (h | h | h) <;>
    (try {omega}) <;>
    (try {norm_num at *; omega})
