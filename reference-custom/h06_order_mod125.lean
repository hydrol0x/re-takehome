import Mathlib

/-- Transfer a numeric `%`-computation into `ZMod 125`. -/
lemma h06_cast_pow (a k r : ℕ) (h : a ^ k % 125 = r) :
    ((a : ZMod 125)) ^ k = ((r : ℕ) : ZMod 125) := by
  rw [← Nat.cast_pow, ← ZMod.natCast_mod (a ^ k) 125, h]

/-- The multiplicative order of `2` in `ZMod 125` is exactly `100`. -/
lemma h06_orderOf : orderOf (2 : ZMod 125) = 100 := by
  have h100 : (2 : ZMod 125) ^ 100 = 1 := by
    have := h06_cast_pow 2 100 1 (by norm_num)
    simpa using this
  have h50 : (2 : ZMod 125) ^ 50 = (124 : ℕ) := by
    have := h06_cast_pow 2 50 124 (by norm_num)
    simpa using this
  have h20 : (2 : ZMod 125) ^ 20 = (76 : ℕ) := by
    have := h06_cast_pow 2 20 76 (by norm_num)
    simpa using this
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) h100
  intro p hp hpd
  have hp25 : p = 2 ∨ p = 5 := by
    have h4 : p ∣ 4 * 25 := (by norm_num : (100 : ℕ) = 4 * 25) ▸ hpd
    rcases (Nat.Prime.dvd_mul hp).mp h4 with hd | hd
    · left
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
        (hp.dvd_of_dvd_pow (show p ∣ 2 ^ 2 by norm_num; exact hd))
    · right
      exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp
        (hp.dvd_of_dvd_pow (show p ∣ 5 ^ 2 by norm_num; exact hd))
  rcases hp25 with rfl | rfl
  · show (2 : ZMod 125) ^ (100 / 2) ≠ 1
    rw [(by norm_num : 100 / 2 = 50), h50]
    decide
  · show (2 : ZMod 125) ^ (100 / 5) ≠ 1
    rw [(by norm_num : 100 / 5 = 20), h20]
    decide

/-- The multiplicative order of `2` modulo `125`. Must be a numeric literal. -/
abbrev h06_answer : ℕ := 100

/-- `h06_answer` is the least positive `n` with `2 ^ n ≡ 1 (mod 125)`. -/
theorem h06_order_mod125 :
    IsLeast {n : ℕ | 0 < n ∧ 2 ^ n % 125 = 1} h06_answer := by
  constructor
  · show 0 < 100 ∧ 2 ^ 100 % 125 = 1
    exact ⟨by norm_num, by norm_num⟩
  · rintro k ⟨hk, hmod⟩
    show 100 ≤ k
    have hcast : (2 : ZMod 125) ^ k = 1 := by
      have := h06_cast_pow 2 k 1 hmod
      simpa using this
    have hdvd := orderOf_dvd_of_pow_eq_one hcast
    rw [h06_orderOf] at hdvd
    exact Nat.le_of_dvd hk hdvd
