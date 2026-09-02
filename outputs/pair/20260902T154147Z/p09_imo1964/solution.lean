import Mathlib

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  constructor
  · -- Forward direction: if 7 divides 2^n - 1, then 3 divides n
    intro h
    have h₁ : 2 ^ n % 7 = 1 := by
      have h₂ : (2 ^ n - 1) % 7 = 0 := Nat.mod_eq_zero_of_dvd h
      have h₃ : 2 ^ n % 7 = 1 := by
        have h₄ : 2 ^ n ≥ 1 := Nat.one_le_pow _ _ (by linarith)
        omega
      exact h₃
    -- Show that n must be divisible by 3
    have h₂ : n % 3 = 0 := by
      have h₃ : ∀ k : ℕ, 2 ^ (3 * k) % 7 = 1 ∧ 2 ^ (3 * k + 1) % 7 = 2 ∧ 2 ^ (3 * k + 2) % 7 = 4 := by
        intro k
        induction k with
        | zero =>
          constructor
          · norm_num
          · constructor
            · norm_num
            · norm_num
        | succ k ih =>
          constructor
          · -- 2^(3*(k+1)) = 2^(3*k + 3) = 2^(3*k) * 8 ≡ 1 * 1 = 1 (mod 7)
            have h₄ : 2 ^ (3 * k + 3) % 7 = 1 := by
              calc
                2 ^ (3 * k + 3) % 7 = (2 ^ (3 * k) * 2 ^ 3) % 7 := by rw [pow_add]
                _ = ((2 ^ (3 * k) % 7) * (2 ^ 3 % 7)) % 7 := by simp [Nat.mul_mod]
                _ = (1 * 1) % 7 := by
                  simp [ih.1, pow_succ, Nat.mul_mod]
                  <;> norm_num
                _ = 1 := by norm_num
            exact h₄
          · constructor
            · -- 2^(3*(k+1)+1) = 2^(3*k + 4) = 2^(3*k) * 16 ≡ 1 * 2 = 2 (mod 7)
              have h₄ : 2 ^ (3 * k + 4) % 7 = 2 := by
                calc
                  2 ^ (3 * k + 4) % 7 = (2 ^ (3 * k) * 2 ^ 4) % 7 := by rw [pow_add]
                  _ = ((2 ^ (3 * k) % 7) * (2 ^ 4 % 7)) % 7 := by simp [Nat.mul_mod]
                  _ = (1 * 2) % 7 := by
                    simp [ih.1, pow_succ, Nat.mul_mod]
                    <;> norm_num
                  _ = 2 := by norm_num
              exact h₄
            · -- 2^(3*(k+1)+2) = 2^(3*k + 5) = 2^(3*k) * 32 ≡ 1 * 4 = 4 (mod 7)
              have h₄ : 2 ^ (3 * k + 5) % 7 = 4 := by
                calc
                  2 ^ (3 * k + 5) % 7 = (2 ^ (3 * k) * 2 ^ 5) % 7 := by rw [pow_add]
                  _ = ((2 ^ (3 * k) % 7) * (2 ^ 5 % 7)) % 7 := by simp [Nat.mul_mod]
                  _ = (1 * 4) % 7 := by
                    simp [ih.1, pow_succ, Nat.mul_mod]
                    <;> norm_num
                  _ = 4 := by norm_num
              exact h₄
      -- Now check which case n falls into
      have h₄ : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases h₄ with (h₄ | h₄ | h₄)
      · exact h₄
      · -- Case n % 3 = 1
        exfalso
        have h₅ := h₃ (n / 3)
        have h₆ : 2 ^ n % 7 = 2 := by
          have h₇ : n = 3 * (n / 3) + 1 := by
            omega
          rw [h₇]
          exact h₅.2.1
        omega
      · -- Case n % 3 = 2
        exfalso
        have h₅ := h₃ (n / 3)
        have h₆ : 2 ^ n % 7 = 4 := by
          have h₇ : n = 3 * (n / 3) + 2 := by
            omega
          rw [h₇]
          exact h₅.2.2
        omega
    -- Since n % 3 = 0, we have 3 ∣ n
    omega
  · -- Backward direction: if 3 divides n, then 7 divides 2^n - 1
    intro h
    have h₁ : ∃ k : ℕ, n = 3 * k := by
      obtain ⟨k, hk⟩ := h
      exact ⟨k, by omega⟩
    obtain ⟨k, hk⟩ := h₁
    have h₂ : 2 ^ n % 7 = 1 := by
      rw [hk]
      have h₃ : ∀ k : ℕ, 2 ^ (3 * k) % 7 = 1 := by
        intro k
        induction k with
        | zero => norm_num
        | succ k ih =>
          calc
            2 ^ (3 * (k + 1)) % 7 = 2 ^ (3 * k + 3) % 7 := by ring_nf
            _ = (2 ^ (3 * k) * 2 ^ 3) % 7 := by rw [pow_add]
            _ = ((2 ^ (3 * k) % 7) * (2 ^ 3 % 7)) % 7 := by simp [Nat.mul_mod]
            _ = (1 * 1) % 7 := by
              simp [ih, pow_succ, Nat.mul_mod]
              <;> norm_num
            _ = 1 := by norm_num
      exact h₃ k
    have h₃ : (2 ^ n - 1) % 7 = 0 := by
      have h₄ : 2 ^ n ≥ 1 := Nat.one_le_pow _ _ (by omega)
      omega
    exact Nat.dvd_of_mod_eq_zero h₃

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  intro h
  have h₁ : (2 ^ n + 1) % 7 = 0 := Nat.mod_eq_zero_of_dvd h
  have h₂ : 2 ^ n % 7 = 6 := by
    have h₃ : (2 ^ n + 1) % 7 = 0 := h₁
    have h₄ : 2 ^ n % 7 = 6 := by
      omega
    exact h₄
  -- Show that 2^n mod 7 can only be 1, 2, or 4
  have h₃ : ∀ k : ℕ, 2 ^ (3 * k) % 7 = 1 ∧ 2 ^ (3 * k + 1) % 7 = 2 ∧ 2 ^ (3 * k + 2) % 7 = 4 := by
    intro k
    induction k with
    | zero =>
      constructor
      · norm_num
      · constructor
        · norm_num
        · norm_num
    | succ k ih =>
      constructor
      · -- 2^(3*(k+1)) = 2^(3*k + 3) = 2^(3*k) * 8 ≡ 1 * 1 = 1 (mod 7)
        have h₄ : 2 ^ (3 * k + 3) % 7 = 1 := by
          calc
            2 ^ (3 * k + 3) % 7 = (2 ^ (3 * k) * 2 ^ 3) % 7 := by rw [pow_add]
            _ = ((2 ^ (3 * k) % 7) * (2 ^ 3 % 7)) % 7 := by simp [Nat.mul_mod]
            _ = (1 * 1) % 7 := by
              simp [ih.1, pow_succ, Nat.mul_mod]
              <;> norm_num
            _ = 1 := by norm_num
        exact h₄
      · constructor
        · -- 2^(3*(k+1)+1) = 2^(3*k + 4) = 2^(3*k) * 16 ≡ 1 * 2 = 2 (mod 7)
          have h₄ : 2 ^ (3 * k + 4) % 7 = 2 := by
            calc
              2 ^ (3 * k + 4) % 7 = (2 ^ (3 * k) * 2 ^ 4) % 7 := by rw [pow_add]
              _ = ((2 ^ (3 * k) % 7) * (2 ^ 4 % 7)) % 7 := by simp [Nat.mul_mod]
              _ = (1 * 2) % 7 := by
                simp [ih.1, pow_succ, Nat.mul_mod]
                <;> norm_num
              _ = 2 := by norm_num
          exact h₄
        · -- 2^(3*(k+1)+2) = 2^(3*k + 5) = 2^(3*k) * 32 ≡ 1 * 4 = 4 (mod 7)
          have h₄ : 2 ^ (3 * k + 5) % 7 = 4 := by
            calc
              2 ^ (3 * k + 5) % 7 = (2 ^ (3 * k) * 2 ^ 5) % 7 := by rw [pow_add]
              _ = ((2 ^ (3 * k) % 7) * (2 ^ 5 % 7)) % 7 := by simp [Nat.mul_mod]
              _ = (1 * 4) % 7 := by
                simp [ih.1, pow_succ, Nat.mul_mod]
                <;> norm_num
              _ = 4 := by norm_num
          exact h₄
  -- Check which case n falls into
  have h₄ : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h₄ with (h₄ | h₄ | h₄)
  · -- Case n % 3 = 0
    have h₅ := h₃ (n / 3)
    have h₆ : 2 ^ n % 7 = 1 := by
      have h₇ : n = 3 * (n / 3) := by omega
      rw [h₇]
      exact h₅.1
    omega
  · -- Case n % 3 = 1
    have h₅ := h₃ (n / 3)
    have h₆ : 2 ^ n % 7 = 2 := by
      have h₇ : n = 3 * (n / 3) + 1 := by omega
      rw [h₇]
      exact h₅.2.1
    omega
  · -- Case n % 3 = 2
    have h₅ := h₃ (n / 3)
    have h₆ : 2 ^ n % 7 = 4 := by
      have h₇ : n = 3 * (n / 3) + 2 := by omega
      rw [h₇]
      exact h₅.2.2
    omega
