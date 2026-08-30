import Mathlib

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  have h_cycle : ∀ k : ℕ, 2 ^ (3 * k) % 7 = 1 ∧ 2 ^ (3 * k + 1) % 7 = 2 ∧ 2 ^ (3 * k + 2) % 7 = 4 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      simp [pow_add, pow_mul, Nat.mul_succ, Nat.add_assoc] at ih ⊢
      omega
  
  constructor
  · -- Forward direction: if 7 ∣ 2^n - 1, then 3 ∣ n
    intro h
    have h_mod : 2 ^ n % 7 = 1 := by
      have h_div : 7 ∣ 2 ^ n - 1 := h
      have h_ge : 2 ^ n ≥ 1 := by
        apply Nat.one_le_pow
        omega
      have h_sub : 2 ^ n - 1 + 1 = 2 ^ n := by
        omega
      rw [← h_sub] at h_div
      exact Nat.mod_eq_zero_of_dvd h_div
    -- Now we know 2^n ≡ 1 (mod 7), so n must be divisible by 3
    have h_n_mod_3 : n % 3 = 0 := by
      by_contra h_not
      have h_rem : n % 3 = 1 ∨ n % 3 = 2 := by
        have h_neq : n % 3 ≠ 0 := h_not
        have h_lt : n % 3 < 3 := Nat.mod_lt n (by decide)
        omega
      cases h_rem with
      | inl h_rem1 =>
        -- Case: n ≡ 1 (mod 3)
        have h_case : ∃ k : ℕ, n = 3 * k + 1 := by
          use n / 3
          have h_div : n = 3 * (n / 3) + n % 3 := by
            rw [Nat.div_add_mod]
          rw [h_rem1] at h_div
          omega
        rcases h_case with ⟨k, rfl⟩
        have h_val := h_cycle k
        have h_mod_val : 2 ^ (3 * k + 1) % 7 = 2 := h_val.2.1
        omega
      | inr h_rem2 =>
        -- Case: n ≡ 2 (mod 3)
        have h_case : ∃ k : ℕ, n = 3 * k + 2 := by
          use n / 3
          have h_div : n = 3 * (n / 3) + n % 3 := by
            rw [Nat.div_add_mod]
          rw [h_rem2] at h_div
          omega
        rcases h_case with ⟨k, rfl⟩
        have h_val := h_cycle k
        have h_mod_val : 2 ^ (3 * k + 2) % 7 = 4 := h_val.2.2
        omega
    exact Nat.dvd_of_mod_eq_zero h_n_mod_3
  · -- Backward direction: if 3 ∣ n, then 7 ∣ 2^n - 1
    intro h
    have h_div : ∃ k : ℕ, n = 3 * k := by
      obtain ⟨k, hk⟩ := h
      exact ⟨k, by linarith⟩
    rcases h_div with ⟨k, rfl⟩
    have h_cycle_val := h_cycle k
    have h_mod : 2 ^ (3 * k) % 7 = 1 := h_cycle_val.1
    have h_ge : 2 ^ (3 * k) ≥ 1 := by
      apply Nat.one_le_pow
      omega
    have h_sub : 2 ^ (3 * k) - 1 + 1 = 2 ^ (3 * k) := by
      omega
    have h_mod_eq : (2 ^ (3 * k) - 1) % 7 = 0 := by
      have h_mod_val : 2 ^ (3 * k) % 7 = 1 := h_cycle_val.1
      have h_sub_mod : (2 ^ (3 * k) - 1) % 7 = 0 := by
        have h_ge' : 2 ^ (3 * k) ≥ 1 := by
          apply Nat.one_le_pow
          omega
        omega
      exact h_sub_mod
    exact Nat.dvd_of_mod_eq_zero h_mod_eq

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  intro h
  have h_mod : (2 ^ n + 1) % 7 = 0 := by
    exact Nat.mod_eq_zero_of_dvd h
  -- Check all possible values of 2^n mod 7
  have h_cycle : ∀ k : ℕ, 2 ^ (3 * k) % 7 = 1 ∧ 2 ^ (3 * k + 1) % 7 = 2 ∧ 2 ^ (3 * k + 2) % 7 = 4 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      simp [pow_add, pow_mul, Nat.mul_succ, Nat.add_assoc] at ih ⊢
      omega
  
  have h_n_mod_3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  cases h_n_mod_3 with
  | inl h_rem0 =>
    -- Case: n ≡ 0 (mod 3)
    have h_case : ∃ k : ℕ, n = 3 * k := by
      use n / 3
      have h_div : n = 3 * (n / 3) + n % 3 := by
        rw [Nat.div_add_mod]
      rw [h_rem0] at h_div
      omega
    rcases h_case with ⟨k, rfl⟩
    have h_val := h_cycle k
    have h_mod_val : 2 ^ (3 * k) % 7 = 1 := h_val.1
    have h_sum_mod : (2 ^ (3 * k) + 1) % 7 = 2 := by
      omega
    omega
  | inr h_rem_rest =>
    cases h_rem_rest with
    | inl h_rem1 =>
      -- Case: n ≡ 1 (mod 3)
      have h_case : ∃ k : ℕ, n = 3 * k + 1 := by
        use n / 3
        have h_div : n = 3 * (n / 3) + n % 3 := by
          rw [Nat.div_add_mod]
        rw [h_rem1] at h_div
        omega
      rcases h_case with ⟨k, rfl⟩
      have h_val := h_cycle k
      have h_mod_val : 2 ^ (3 * k + 1) % 7 = 2 := h_val.2.1
      have h_sum_mod : (2 ^ (3 * k + 1) + 1) % 7 = 3 := by
        omega
      omega
    | inr h_rem2 =>
      -- Case: n ≡ 2 (mod 3)
      have h_case : ∃ k : ℕ, n = 3 * k + 2 := by
        use n / 3
        have h_div : n = 3 * (n / 3) + n % 3 := by
          rw [Nat.div_add_mod]
        rw [h_rem2] at h_div
        omega
      rcases h_case with ⟨k, rfl⟩
      have h_val := h_cycle k
      have h_mod_val : 2 ^ (3 * k + 2) % 7 = 4 := h_val.2.2
      have h_sum_mod : (2 ^ (3 * k + 2) + 1) % 7 = 5 := by
        omega
      omega
