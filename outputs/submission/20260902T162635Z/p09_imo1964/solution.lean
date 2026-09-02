import Mathlib

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  constructor
  · -- Forward direction: if 7 divides 2^n - 1, then 3 divides n
    intro h
    have h₁ : ∀ k : ℕ, 2 ^ k % 7 = (2 ^ (k % 3)) % 7 := by
      intro k
      rw [← Nat.mod_add_div k 3]
      simp [pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
      <;> norm_num
      <;> rfl
    have h₂ : 2 ^ n % 7 = 1 := by
      have h₃ : 7 ∣ 2 ^ n - 1 := h
      have h₄ : (2 ^ n - 1) % 7 = 0 := Nat.mod_eq_zero_of_dvd h₃
      have h₅ : 2 ^ n % 7 = 1 := by
        have h₆ : 2 ^ n ≥ 1 := by
          apply Nat.one_le_pow
          omega
        have h₇ : (2 ^ n - 1) % 7 = 0 := h₄
        have h₈ : 2 ^ n % 7 = 1 := by
          omega
        exact h₈
      exact h₅
    have h₃ : 2 ^ (n % 3) % 7 = 1 := by
      rw [h₁] at h₂
      exact h₂
    have h₄ : n % 3 = 0 := by
      have h₅ : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases h₅ with (h₅ | h₅ | h₅)
      · exact h₅
      · exfalso
        rw [h₅] at h₃
        norm_num at h₃
      · exfalso
        rw [h₅] at h₃
        norm_num at h₃
    omega
  · -- Backward direction: if 3 divides n, then 7 divides 2^n - 1
    intro h
    obtain ⟨k, hk⟩ := h
    rw [hk]
    have h₁ : ∀ m : ℕ, 7 ∣ 2 ^ (3 * m) - 1 := by
      intro m
      induction m with
      | zero =>
        simp
      | succ m ih =>
        simp [Nat.mul_succ, pow_add, pow_one, Nat.pow_succ] at ih ⊢
        ring_nf at ih ⊢
        omega
    exact h₁ k

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  intro h
  have h₁ : ∀ k : ℕ, 2 ^ k % 7 = (2 ^ (k % 3)) % 7 := by
    intro k
    rw [← Nat.mod_add_div k 3]
    simp [pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
    <;> norm_num
    <;> rfl
  have h₂ : (2 ^ n + 1) % 7 = 0 := by
    have h₃ : 7 ∣ 2 ^ n + 1 := h
    exact Nat.mod_eq_zero_of_dvd h₃
  have h₃ : 2 ^ n % 7 = 6 := by
    have h₄ : (2 ^ n + 1) % 7 = 0 := h₂
    have h₅ : 2 ^ n % 7 = 6 := by
      omega
    exact h₅
  have h₄ : 2 ^ (n % 3) % 7 = 6 := by
    rw [h₁] at h₃
    exact h₃
  have h₅ : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h₅ with (h₅ | h₅ | h₅)
  · exfalso
    rw [h₅] at h₄
    norm_num at h₄
  · exfalso
    rw [h₅] at h₄
    norm_num at h₄
  · exfalso
    rw [h₅] at h₄
    norm_num at h₄