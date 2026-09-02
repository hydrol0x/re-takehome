import Mathlib

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  constructor
  · -- Forward direction: if 7 | 2^n - 1, then 3 | n
    intro h
    have h1 : 2 ^ n % 7 = 1 := by
      have : 7 ∣ 2 ^ n - 1 := h
      have : (2 ^ n - 1) % 7 = 0 := by
        simpa [Nat.dvd_iff_mod_eq_zero] using this
      have : 2 ^ n % 7 = 1 := by
        have : 2 ^ n ≥ 1 := by
          apply Nat.one_le_pow
          omega
        have : 2 ^ n - 1 + 1 = 2 ^ n := by
          omega
        omega
      exact this
    -- Now check what n % 3 must be given 2^n % 7 = 1
    have : n % 3 = 0 := by
      have : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases this with (h3 | h3 | h3) <;>
        (try omega) <;>
        (try {
          have h2 : 2 ^ n % 7 = (2 ^ (n % 3)) % 7 := by
            rw [← Nat.mod_add_div n 3]
            rw [pow_add, pow_mul]
            simp [h3, Nat.pow_mod, Nat.mul_mod, Nat.mod_mod]
            <;> ring_nf <;> simp [h3]
            <;> norm_num
          rw [h3] at h2
          omega
        })
    omega
  · -- Backward direction: if 3 | n, then 7 | 2^n - 1
    intro h
    obtain ⟨k, rfl⟩ := h
    have : 2 ^ (3 * k) % 7 = 1 := by
      induction k with
      | zero => simp
      | succ k ih =>
        simp [pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod] at *
        <;> norm_num at * <;> omega
    rw [← Nat.mod_add_div (2 ^ (3 * k)) 7]
    simp [this, Nat.dvd_iff_mod_eq_zero]
    <;> omega

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  intro h
  have h1 : (2 ^ n + 1) % 7 = 0 := by
    simpa [Nat.dvd_iff_mod_eq_zero] using h
  -- Check all possible values of n % 3
  have : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases this with (h3 | h3 | h3)
  · -- Case n % 3 = 0
    have h2 : 2 ^ n % 7 = 1 := by
      have : 2 ^ n % 7 = (2 ^ (n % 3)) % 7 := by
        rw [← Nat.mod_add_div n 3]
        rw [pow_add, pow_mul]
        simp [h3, Nat.pow_mod, Nat.mul_mod, Nat.mod_mod]
        <;> ring_nf <;> simp [h3]
        <;> norm_num
      rw [h3] at this
      norm_num at this ⊢
      omega
    omega
  · -- Case n % 3 = 1
    have h2 : 2 ^ n % 7 = 2 := by
      have : 2 ^ n % 7 = (2 ^ (n % 3)) % 7 := by
        rw [← Nat.mod_add_div n 3]
        rw [pow_add, pow_mul]
        simp [h3, Nat.pow_mod, Nat.mul_mod, Nat.mod_mod]
        <;> ring_nf <;> simp [h3]
        <;> norm_num
      rw [h3] at this
      norm_num at this ⊢
      omega
    omega
  · -- Case n % 3 = 2
    have h2 : 2 ^ n % 7 = 4 := by
      have : 2 ^ n % 7 = (2 ^ (n % 3)) % 7 := by
        rw [← Nat.mod_add_div n 3]
        rw [pow_add, pow_mul]
        simp [h3, Nat.pow_mod, Nat.mul_mod, Nat.mod_mod]
        <;> ring_nf <;> simp [h3]
        <;> norm_num
      rw [h3] at this
      norm_num at this ⊢
      omega
    omega
