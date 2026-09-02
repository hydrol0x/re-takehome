import Mathlib

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/


theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  constructor
  · intro h
    -- If 7 divides 2^n - 1, then 2^n ≡ 1 (mod 7)
    have : 2 ^ n % 7 = 1 := by
      rw [Nat.dvd_iff_mod_eq_zero] at h
      have : (2 ^ n - 1) % 7 = 0 := h
      have : 2 ^ n % 7 = 1 := by
        omega
      exact this
    -- Show that n ≡ 0 (mod 3)
    have : n % 3 = 0 := by
      have : ∀ k : ℕ, 2 ^ k % 7 = match k % 3 with
        | 0 => 1
        | 1 => 2
        | 2 => 4
      | _ => sorry
      sorry
    exact Nat.mod_eq_zero_of_dvd this
  · intro h
    -- If 3 divides n, then 2^n ≡ 1 (mod 7)
    have : 2 ^ n % 7 = 1 := by
      have : n % 3 = 0 := Nat.mod_eq_zero_of_dvd h
      sorry
    rw [Nat.dvd_iff_mod_eq_zero]
    omega

I'll focus on proving the modular arithmetic properties systematically. The key is understanding how powers of 2 behave modulo 7, which follows a predictable 3-step cycle.

By examining the pattern of 2^n mod 7, I can see a clear relationship between the exponent's remainder when divided by 3 and the resulting modular value. This suggests a structured approach to proving divisibility conditions.

The theorem requires showing both directions of the equivalence, carefully tracking how the modular arithmetic constrains the possible values of n.
</think>
