import Mathlib

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  have h_cycle : ∀ k : ℕ, (2 ^ (3 * k)) % 7 = 1 ∧ (2 ^ (3 * k + 1)) % 7 = 2 ∧ (2 ^ (3 * k + 2)) % 7 = 4 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      simp [pow_add, pow_mul, Nat.mul_succ, Nat.pow_mod] at ih ⊢
      norm_num at ih ⊢
      omega
  
  constructor
  · -- Forward direction: if 7 ∣ 2^n - 1, then 3 ∣ n
    intro h
    have h_mod : (2 ^ n) % 7 = 1 := by
      have h₁ : (2 ^ n - 1) % 7 = 0 := by
        exact Nat.mod_eq_zero_of_dvd h
      have h₂ : (2 ^ n) % 7 = 1 := by
        have h₃ : 2 ^ n ≥ 1 := by
          apply Nat.one_le_pow
          linarith
        have h₄ : (2 ^ n - 1) % 7 = 0 := h₁
        have h₅ : (2 ^ n) % 7 = 1 := by
          have h₆ := Nat.mod_add_div (2 ^ n) 7
          omega
        exact h₅
      exact h₂
    
    have h_case : n % 3 = 0 := by
      have h₁ := h_cycle (n / 3)
      have h₂ : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases h₂ with (h₂ | h₂ | h₂)
      · exact h₂
      · -- Case n % 3 = 1
        have h₃ : (2 ^ n) % 7 = 2 := by
          have h₄ : n = 3 * (n / 3) + 1 := by omega
          rw [h₄]
          exact (h_cycle (n / 3)).right.left
        omega
      · -- Case n % 3 = 2
        have h₃ : (2 ^ n) % 7 = 4 := by
          have h₄ : n = 3 * (n / 3) + 2 := by omega
          rw [h₄]
          exact (h_cycle (n / 3)).right.right
        omega
    
    exact Nat.dvd_of_mod_eq_zero h_case
  
  · -- Backward direction: if 3 ∣ n, then 7 ∣ 2^n - 1
    intro h
    obtain ⟨k, hk⟩ := h
    have h₁ : n = 3 * k := by omega
    rw [h₁]
    have h₂ : (2 ^ (3 * k)) % 7 = 1 := (h_cycle k).left
    have h₃ : (2 ^ (3 * k) - 1) % 7 = 0 := by
      have h₄ : 2 ^ (3 * k) ≥ 1 := by
        apply Nat.one_le_pow
        linarith
      omega
    exact Nat.dvd_of_mod_eq_zero h₃

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  intro h
  have h_cycle : ∀ k : ℕ, (2 ^ (3 * k)) % 7 = 1 ∧ (2 ^ (3 * k + 1)) % 7 = 2 ∧ (2 ^ (3 * k + 2)) % 7 = 4 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      simp [pow_add, pow_mul, Nat.mul_succ, Nat.pow_mod] at ih ⊢
      norm_num at ih ⊢
      omega
  
  have h_mod : (2 ^ n + 1) % 7 = 0 := by
    exact Nat.mod_eq_zero_of_dvd h
  
  have h_case : False := by
    have h₁ : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases h₁ with (h₁ | h₁ | h₁)
    · -- Case n % 3 = 0
      have h₂ : (2 ^ n) % 7 = 1 := by
        have h₃ : n = 3 * (n / 3) := by omega
        rw [h₃]
        exact (h_cycle (n / 3)).left
      have h₃ : (2 ^ n + 1) % 7 = 2 := by
        omega
      omega
    · -- Case n % 3 = 1
      have h₂ : (2 ^ n) % 7 = 2 := by
        have h₃ : n = 3 * (n / 3) + 1 := by omega
        rw [h₃]
        exact (h_cycle (n / 3)).right.left
      have h₃ : (2 ^ n + 1) % 7 = 3 := by
        omega
      omega
    · -- Case n % 3 = 2
      have h₂ : (2 ^ n) % 7 = 4 := by
        have h₃ : n = 3 * (n / 3) + 2 := by omega
        rw [h₃]
        exact (h_cycle (n / 3)).right.right
      have h₃ : (2 ^ n + 1) % 7 = 5 := by
        omega
      omega
  
  exact h_case
