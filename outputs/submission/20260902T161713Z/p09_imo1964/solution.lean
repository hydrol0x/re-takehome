import Mathlib

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  have h_pow_mod_7 : ∀ k : ℕ, (2 ^ k) % 7 = 
    if k % 3 = 0 then 1
    else if k % 3 = 1 then 2
    else 4 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      simp [ih, Nat.mul_mod, Nat.add_mod]
      split_ifs <;> norm_num <;> omega
  
  constructor
  · -- Forward: if 7 ∣ 2^n - 1, then 3 ∣ n
    intro h
    have h₁ : (2 ^ n) % 7 = 1 := by
      have h₂ : (2 ^ n - 1) % 7 = 0 := Nat.mod_eq_zero_of_dvd h
      have h₃ : (2 ^ n) % 7 = 1 := by
        have h₄ : 2 ^ n ≥ 1 := Nat.one_le_pow _ _ (by linarith)
        have h₅ : (2 ^ n - 1) % 7 = 0 := h₂
        have h₆ : (2 ^ n) % 7 = 1 := by
          rw [← Nat.mod_add_div (2 ^ n) 7]
          omega
        exact h₆
      exact h₃
    have h₂ : n % 3 = 0 := by
      have h₃ := h_pow_mod_7 n
      rw [h₁] at h₃
      split_ifs at h₃ <;> try omega
    exact Nat.dvd_of_mod_eq_zero h₂
  · -- Backward: if 3 ∣ n, then 7 ∣ 2^n - 1
    intro h
    have h₁ : n % 3 = 0 := Nat.mod_eq_zero_of_dvd h
    have h₂ : (2 ^ n) % 7 = 1 := by
      have h₃ := h_pow_mod_7 n
      rw [h₁] at h₃
      split_ifs at h₃ <;> simp_all
    have h₃ : 7 ∣ 2 ^ n - 1 := by
      have h₄ : 2 ^ n ≥ 1 := Nat.one_le_pow _ _ (by linarith)
      have h₅ : (2 ^ n) % 7 = 1 := h₂
      have h₆ : (2 ^ n - 1) % 7 = 0 := by
        rw [← Nat.mod_add_div (2 ^ n) 7]
        omega
      exact Nat.dvd_of_mod_eq_zero h₆
    exact h₃

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  have h_pow_mod_7 : ∀ k : ℕ, (2 ^ k) % 7 = 
    if k % 3 = 0 then 1
    else if k % 3 = 1 then 2
    else 4 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      simp [ih, Nat.mul_mod, Nat.add_mod]
      split_ifs <;> norm_num <;> omega
  
  intro h
  have h₁ : (2 ^ n + 1) % 7 = 0 := Nat.mod_eq_zero_of_dvd h
  have h₂ : (2 ^ n) % 7 = 6 := by
    have h₃ : (2 ^ n + 1) % 7 = 0 := h₁
    have h₄ : (2 ^ n) % 7 = 6 := by
      omega
    exact h₄
  have h₃ := h_pow_mod_7 n
  rw [h₂] at h₃
  split_ifs at h₃ <;> omega