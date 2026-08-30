import Mathlib

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  have h_main : ∀ k : ℕ, 2 ^ (3 * k) % 7 = 1 ∧ 2 ^ (3 * k + 1) % 7 = 2 ∧ 2 ^ (3 * k + 2) % 7 = 4 := by
    intro k
    induction k with
    | zero =>
      constructor
      · norm_num
      · constructor
        · norm_num
        · norm_num
    | succ k ih =>
      simp [pow_add, pow_mul, Nat.mul_succ, Nat.pow_succ] at ih ⊢
      constructor
      · omega
      · constructor
        · omega
        · omega
  
  constructor
  · -- Forward direction: if 7 ∣ 2^n - 1, then 3 ∣ n
    intro h
    have h_mod : 2 ^ n % 7 = 1 := by
      have h_dvd : 7 ∣ 2 ^ n - 1 := h
      have h_mod' : (2 ^ n - 1) % 7 = 0 := Nat.mod_eq_zero_of_dvd h_dvd
      have h_pow_mod : 2 ^ n % 7 = 1 := by
        have h_ge : 2 ^ n ≥ 1 := by
          apply Nat.one_le_pow
          linarith
        have h_sub_mod : (2 ^ n - 1) % 7 = (2 ^ n % 7 - 1) % 7 := by
          rw [← Nat.mod_add_div (2 ^ n) 7]
          simp [Nat.sub_sub_self, Nat.add_sub_assoc, Nat.mod_mod]
          <;> omega
        omega
      exact h_pow_mod
    -- Now we know 2^n ≡ 1 (mod 7), so n must be divisible by 3
    have h_case : n % 3 = 0 := by
      by_contra h_not
      have h_rem : n % 3 = 1 ∨ n % 3 = 2 := by
        have h_neq : n % 3 ≠ 0 := h_not
        have h_lt : n % 3 < 3 := Nat.mod_lt n (by norm_num)
        omega
      cases h_rem with
      | inl h_rem1 =>
        have h_k : ∃ k, n = 3 * k + 1 := by
          use n / 3
          have h_div : n = 3 * (n / 3) + n % 3 := Nat.div_add_mod n 3
          rw [h_rem1] at h_div
          omega
        obtain ⟨k, hk⟩ := h_k
        have h_pow := h_main k
        rw [hk] at h_mod
        have h_val : 2 ^ (3 * k + 1) % 7 = 2 := h_pow.2.1
        omega
      | inr h_rem2 =>
        have h_k : ∃ k, n = 3 * k + 2 := by
          use n / 3
          have h_div : n = 3 * (n / 3) + n % 3 := Nat.div_add_mod n 3
          rw [h_rem2] at h_div
          omega
        obtain ⟨k, hk⟩ := h_k
        have h_pow := h_main k
        rw [hk] at h_mod
        have h_val : 2 ^ (3 * k + 2) % 7 = 4 := h_pow.2.2
        omega
    exact Nat.dvd_of_mod_eq_zero h_case
  · -- Backward direction: if 3 ∣ n, then 7 ∣ 2^n - 1
    intro h
    have h_k : ∃ k, n = 3 * k := by
      exact Nat.exists_eq_mul_left_of_dvd h
    obtain ⟨k, hk⟩ := h_k
    have h_pow := h_main k
    have h_mod : 2 ^ n % 7 = 1 := by
      rw [hk]
      exact h_pow.1
    have h_sub : (2 ^ n - 1) % 7 = 0 := by
      have h_ge : 2 ^ n ≥ 1 := by
        apply Nat.one_le_pow
        linarith
      omega
    exact Nat.dvd_of_mod_eq_zero h_sub

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  have h_main : ∀ k : ℕ, 2 ^ (3 * k) % 7 = 1 ∧ 2 ^ (3 * k + 1) % 7 = 2 ∧ 2 ^ (3 * k + 2) % 7 = 4 := by
    intro k
    induction k with
    | zero =>
      constructor
      · norm_num
      · constructor
        · norm_num
        · norm_num
    | succ k ih =>
      simp [pow_add, pow_mul, Nat.mul_succ, Nat.pow_succ] at ih ⊢
      constructor
      · omega
      · constructor
        · omega
        · omega
  
  intro h
  have h_mod : (2 ^ n + 1) % 7 = 0 := Nat.mod_eq_zero_of_dvd h
  have h_case : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h_case with (h_case | h_case | h_case)
  · -- Case n ≡ 0 (mod 3)
    have h_k : ∃ k, n = 3 * k := by
      use n / 3
      have h_div : n = 3 * (n / 3) + n % 3 := Nat.div_add_mod n 3
      rw [h_case] at h_div
      omega
    obtain ⟨k, hk⟩ := h_k
    have h_pow := h_main k
    have h_val : 2 ^ n % 7 = 1 := by
      rw [hk]
      exact h_pow.1
    have h_sum : (2 ^ n + 1) % 7 = 2 := by
      omega
    omega
  · -- Case n ≡ 1 (mod 3)
    have h_k : ∃ k, n = 3 * k + 1 := by
      use n / 3
      have h_div : n = 3 * (n / 3) + n % 3 := Nat.div_add_mod n 3
      rw [h_case] at h_div
      omega
    obtain ⟨k, hk⟩ := h_k
    have h_pow := h_main k
    have h_val : 2 ^ n % 7 = 2 := by
      rw [hk]
      exact h_pow.2.1
    have h_sum : (2 ^ n + 1) % 7 = 3 := by
      omega
    omega
  · -- Case n ≡ 2 (mod 3)
    have h_k : ∃ k, n = 3 * k + 2 := by
      use n / 3
      have h_div : n = 3 * (n / 3) + n % 3 := Nat.div_add_mod n 3
      rw [h_case] at h_div
      omega
    obtain ⟨k, hk⟩ := h_k
    have h_pow := h_main k
    have h_val : 2 ^ n % 7 = 4 := by
      rw [hk]
      exact h_pow.2.2
    have h_sum : (2 ^ n + 1) % 7 = 5 := by
      omega
    omega
