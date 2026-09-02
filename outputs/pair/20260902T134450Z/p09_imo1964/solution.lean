import Mathlib

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  have h_mod : ∀ k : ℕ, 2 ^ (3 * k) % 7 = 1 ∧ 2 ^ (3 * k + 1) % 7 = 2 ∧ 2 ^ (3 * k + 2) % 7 = 4 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      simp [pow_add, pow_mul, Nat.mul_succ, Nat.pow_succ, Nat.add_assoc] at ih ⊢
      omega
  
  constructor
  · -- Forward direction: if 7 ∣ 2^n - 1, then 3 ∣ n
    intro h
    have h₁ : 2 ^ n % 7 = 1 := by
      have h₂ : 7 ∣ 2 ^ n - 1 := h
      have h₃ : 2 ^ n ≥ 1 := by
        apply Nat.one_le_pow
        linarith
      have h₄ : (2 ^ n - 1) % 7 = 0 := Nat.mod_eq_zero_of_dvd h₂
      have h₅ : 2 ^ n % 7 = 1 := by
        have h₆ : 2 ^ n % 7 = (2 ^ n - 1 + 1) % 7 := by
          rw [Nat.add_comm]
          <;> omega
        omega
      exact h₅
    -- Now show that n must be divisible by 3
    have h₂ : n % 3 = 0 := by
      by_contra h₃
      have h₄ : n % 3 = 1 ∨ n % 3 = 2 := by
        have h₅ : n % 3 ≠ 0 := h₃
        have h₆ : n % 3 < 3 := Nat.mod_lt n (by norm_num)
        omega
      cases h₄ with
      | inl h₄ =>
        -- Case: n ≡ 1 (mod 3)
        have h₅ : ∃ k : ℕ, n = 3 * k + 1 := by
          use n / 3
          have h₆ := Nat.div_add_mod n 3
          omega
        rcases h₅ with ⟨k, rfl⟩
        have h₆ := h_mod k
        have h₇ : 2 ^ (3 * k + 1) % 7 = 2 := h₆.2.1
        omega
      | inr h₄ =>
        -- Case: n ≡ 2 (mod 3)
        have h₅ : ∃ k : ℕ, n = 3 * k + 2 := by
          use n / 3
          have h₆ := Nat.div_add_mod n 3
          omega
        rcases h₅ with ⟨k, rfl⟩
        have h₆ := h_mod k
        have h₇ : 2 ^ (3 * k + 2) % 7 = 4 := h₆.2.2
        omega
    exact Nat.dvd_of_mod_eq_zero h₂
  · -- Reverse direction: if 3 ∣ n, then 7 ∣ 2^n - 1
    intro h
    have h₁ : ∃ k : ℕ, n = 3 * k := by
      obtain ⟨k, hk⟩ := h
      exact ⟨k, by linarith⟩
    rcases h₁ with ⟨k, rfl⟩
    have h₂ : 2 ^ (3 * k) % 7 = 1 := (h_mod k).1
    have h₃ : 7 ∣ 2 ^ (3 * k) - 1 := by
      have h₄ : 2 ^ (3 * k) ≥ 1 := by
        apply Nat.one_le_pow
        linarith
      have h₅ : (2 ^ (3 * k) - 1) % 7 = 0 := by
        have h₆ : 2 ^ (3 * k) % 7 = 1 := h₂
        omega
      exact Nat.dvd_of_mod_eq_zero h₅
    exact h₃

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  have h_mod : ∀ k : ℕ, 2 ^ (3 * k) % 7 = 1 ∧ 2 ^ (3 * k + 1) % 7 = 2 ∧ 2 ^ (3 * k + 2) % 7 = 4 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      simp [pow_add, pow_mul, Nat.mul_succ, Nat.pow_succ, Nat.add_assoc] at ih ⊢
      omega
  
  intro h
  have h₁ : (2 ^ n + 1) % 7 = 0 := Nat.mod_eq_zero_of_dvd h
  have h₂ : 2 ^ n % 7 = 6 := by
    omega
  
  -- Show that 2^n mod 7 cannot be 6
  have h₃ : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  cases h₃ with
  | inl h₃ =>
    -- Case: n ≡ 0 (mod 3)
    have h₄ : ∃ k : ℕ, n = 3 * k := by
      use n / 3
      have h₅ := Nat.div_add_mod n 3
      omega
    rcases h₄ with ⟨k, rfl⟩
    have h₅ := h_mod k
    have h₆ : 2 ^ (3 * k) % 7 = 1 := h₅.1
    omega
  | inr h₃ =>
    cases h₃ with
    | inl h₃ =>
      -- Case: n ≡ 1 (mod 3)
      have h₄ : ∃ k : ℕ, n = 3 * k + 1 := by
        use n / 3
        have h₅ := Nat.div_add_mod n 3
        omega
      rcases h₄ with ⟨k, rfl⟩
      have h₅ := h_mod k
      have h₆ : 2 ^ (3 * k + 1) % 7 = 2 := h₅.2.1
      omega
    | inr h₃ =>
      -- Case: n ≡ 2 (mod 3)
      have h₄ : ∃ k : ℕ, n = 3 * k + 2 := by
        use n / 3
        have h₅ := Nat.div_add_mod n 3
        omega
      rcases h₄ with ⟨k, rfl⟩
      have h₅ := h_mod k
      have h₆ : 2 ^ (3 * k + 2) % 7 = 4 := h₅.2.2
      omega
