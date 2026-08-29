import Mathlib

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by sorry

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  intro h
  rw [Nat.dvd_iff_mod_eq_zero] at h
  have h1 : (2 ^ n) % 7 = 1 ∨ (2 ^ n) % 7 = 2 ∨ (2 ^ n) % 7 = 4 := by
    have : ∀ m : ℕ, (2 ^ m) % 7 = 1 ∨ (2 ^ m) % 7 = 2 ∨ (2 ^ m) % 7 = 4 := by
      intro m
      induction' m using Nat.strong_induction_on with m ih
      match m with
      | 0 => exact Or.inl (by norm_num)
      | k + 1 =>
        have := ih k (by omega)
        rcases this with (h | h | h) <;>
          simp [pow_succ, Nat.mul_mod, h] <;>
          (try omega) <;> (try { norm_num; omega }) <;>
          (try { left; omega }) <;>
          (try { right; omega }) <;>
          (try { right; right; omega })
    exact this n
  rcases h1 with (h1 | h1 | h1)
  · omega
  · omega
  · omega
