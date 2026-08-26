import Mathlib

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  have h_cycle : ∀ k : ℕ, 2 ^ (3 * k) % 7 = 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      simp [pow_add, pow_mul, Nat.mul_succ, Nat.pow_succ] at ih ⊢
      norm_num at ih ⊢
      omega
  
  have h_not_one : ∀ k : ℕ, 2 ^ (3 * k + 1) % 7 = 2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      simp [pow_add, pow_mul, Nat.mul_succ, Nat.pow_succ] at ih ⊢
      norm_num at ih ⊢
      omega
  
  have h_not_two : ∀ k : ℕ, 2 ^ (3 * k + 2) % 7 = 4 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      simp [pow_add, pow_mul, Nat.mul_succ, Nat.pow_succ] at ih ⊢
      norm_num at ih ⊢
      omega
  
  constructor
  · -- Forward direction: if 7 ∣ 2^n - 1, then 3 ∣ n
    intro h
    have h_mod : (2 ^ n - 1) % 7 = 0 := by
      rw [← Nat.mod_eq_zero_of_dvd h]
    have h_mod2 : (2 ^ n) % 7 = 1 := by
      have h_sub : 2 ^ n ≥ 1 := by
        apply Nat.one_le_pow
        linarith
      have h_val : (2 ^ n - 1) % 7 = 0 := h_mod
      omega
    -- Now check which case n falls into (mod 3)
    have h_cases : n % 3 = 0 := by
      have h_rem : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases h_rem with (h_rem | h_rem | h_rem)
      · exact h_rem
      · -- Case n ≡ 1 (mod 3)
        have h_case : ∃ k, n = 3 * k + 1 := by
          use n / 3
          omega
        rcases h_case with ⟨k, rfl⟩
        have : (2 ^ (3 * k + 1)) % 7 = 2 := h_not_one k
        omega
      · -- Case n ≡ 2 (mod 3)
        have h_case : ∃ k, n = 3 * k + 2 := by
          use n / 3
          omega
        rcases h_case with ⟨k, rfl⟩
        have : (2 ^ (3 * k + 2)) % 7 = 4 := h_not_two k
        omega
    -- If n % 3 = 0, then 3 ∣ n
    omega
  · -- Backward direction: if 3 ∣ n, then 7 ∣ 2^n - 1
    intro h
    obtain ⟨k, rfl⟩ := h
    have h_mod : (2 ^ (3 * k)) % 7 = 1 := h_cycle k
    have h_ge : 2 ^ (3 * k) ≥ 1 := by
      apply Nat.one_le_pow
      omega
    have h_div : (2 ^ (3 * k) - 1) % 7 = 0 := by
      omega
    omega

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  intro h
  have h_mod : (2 ^ n + 1) % 7 = 0 := by
    rw [← Nat.mod_eq_zero_of_dvd h]
  
  -- Check all three cases for n % 3
  have h_cases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h_cases with (h_rem | h_rem | h_rem)
  · -- Case n ≡ 0 (mod 3)
    have h_case : ∃ k, n = 3 * k := by
      use n / 3
      omega
    rcases h_case with ⟨k, rfl⟩
    have : (2 ^ (3 * k)) % 7 = 1 := by
      have h_cycle : ∀ m : ℕ, (2 ^ (3 * m)) % 7 = 1 := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
          simp [pow_add, pow_mul, Nat.mul_succ, Nat.pow_succ] at ih ⊢
          norm_num at ih ⊢
          omega
      exact h_cycle k
    omega
  · -- Case n ≡ 1 (mod 3)
    have h_case : ∃ k, n = 3 * k + 1 := by
      use n / 3
      omega
    rcases h_case with ⟨k, rfl⟩
    have : (2 ^ (3 * k + 1)) % 7 = 2 := by
      have h_cycle : ∀ m : ℕ, (2 ^ (3 * m + 1)) % 7 = 2 := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
          simp [pow_add, pow_mul, Nat.mul_succ, Nat.pow_succ] at ih ⊢
          norm_num at ih ⊢
          omega
      exact h_cycle k
    omega
  · -- Case n ≡ 2 (mod 3)
    have h_case : ∃ k, n = 3 * k + 2 := by
      use n / 3
      omega
    rcases h_case with ⟨k, rfl⟩
    have : (2 ^ (3 * k + 2)) % 7 = 4 := by
      have h_cycle : ∀ m : ℕ, (2 ^ (3 * m + 2)) % 7 = 4 := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
          simp [pow_add, pow_mul, Nat.mul_succ, Nat.pow_succ] at ih ⊢
          norm_num at ih ⊢
          omega
      exact h_cycle k
    omega
