import Mathlib

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  have h_mod : ∀ k : ℕ, 2 ^ k % 7 = if k % 3 = 0 then 1 else if k % 3 = 1 then 2 else 4 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      match k with
      | 0 => simp
      | k + 1 =>
        have h₁ := ih (k) (by omega)
        simp [h₁, pow_succ, Nat.mul_mod, Nat.add_mod]
        split_ifs <;> omega
  
  constructor
  · -- Forward direction: if 7 ∣ 2^n - 1, then 3 ∣ n
    intro h
    have h₁ : (2 ^ n) % 7 = 1 := by
      have h₂ : 7 ∣ 2 ^ n - 1 := h
      have h₃ : (2 ^ n - 1) % 7 = 0 := Nat.mod_eq_zero_of_dvd h₂
      have h₄ : 2 ^ n ≥ 1 := by
        apply Nat.one_le_pow
        omega
      have h₅ : (2 ^ n - 1) % 7 = ((2 ^ n) % 7 - 1) % 7 := by
        rw [← Nat.mod_add_div (2 ^ n) 7]
        simp [Nat.sub_sub, Nat.mul_mod, Nat.add_mod]
        <;> omega
      omega
    have h₂ := h_mod n
    rw [h₂] at h₁
    split_ifs at h₁ <;> try omega
  · -- Backward direction: if 3 ∣ n, then 7 ∣ 2^n - 1
    intro h
    have h₁ : n % 3 = 0 := Nat.mod_eq_zero_of_dvd h
    have h₂ := h_mod n
    rw [h₁] at h₂
    simp at h₂
    have h₃ : (2 ^ n) % 7 = 1 := by simpa using h₂
    have h₄ : 2 ^ n ≥ 1 := by
      apply Nat.one_le_pow
      omega
    have h₅ : (2 ^ n - 1) % 7 = 0 := by
      have h₆ : (2 ^ n) % 7 = 1 := h₃
      have h₇ : 2 ^ n ≥ 1 := h₄
      omega
    exact Nat.dvd_of_mod_eq_zero h₅

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  have h_mod : ∀ k : ℕ, 2 ^ k % 7 = if k % 3 = 0 then 1 else if k % 3 = 1 then 2 else 4 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      match k with
      | 0 => simp
      | k + 1 =>
        have h₁ := ih (k) (by omega)
        simp [h₁, pow_succ, Nat.mul_mod, Nat.add_mod]
        split_ifs <;> omega
  
  intro h
  have h₁ : (2 ^ n + 1) % 7 = 0 := Nat.mod_eq_zero_of_dvd h
  have h₂ : (2 ^ n) % 7 = 6 := by
    have h₃ : (2 ^ n + 1) % 7 = 0 := h₁
    have h₄ : 2 ^ n % 7 = 6 := by
      omega
    exact h₄
  have h₃ := h_mod n
  rw [h₃] at h₂
  split_ifs at h₂ <;> omega
