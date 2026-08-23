import Mathlib

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  constructor
  · -- Forward direction: if 7 | 2^n - 1, then 3 | n
    intro h
    have : n % 3 = 0 := by
      by_contra h'
      have h₁ : n % 3 = 1 ∨ n % 3 = 2 := by
        have : n % 3 ≠ 0 := h'
        have : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
        omega
      cases h₁ with
      | inl h₁ =>
        -- Case n ≡ 1 (mod 3)
        have h₂ : (2 ^ n) % 7 = 2 := by
          have : n % 3 = 1 := h₁
          have : (2 ^ n) % 7 = (2 ^ 1) % 7 := by
            rw [← Nat.div_add_mod n 3]
            simp [pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod, this]
            <;> norm_num <;> simp [Nat.pow_mod] <;> decide
          norm_num at this ⊢
          <;> omega
        have h₃ : (2 ^ n - 1) % 7 = 1 := by
          have : (2 ^ n) % 7 = 2 := h₂
          have : 2 ^ n ≥ 1 := Nat.one_le_pow _ _ (by omega)
          have : (2 ^ n - 1) % 7 = ((2 ^ n) % 7 - 1) % 7 := by
            rw [← Nat.mod_add_div (2 ^ n) 7]
            simp [Nat.sub_eq_zero_iff_le, Nat.add_mod, Nat.mul_mod, this]
            <;> omega
          omega
        have : (2 ^ n - 1) % 7 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
        omega
      | inr h₁ =>
        -- Case n ≡ 2 (mod 3)
        have h₂ : (2 ^ n) % 7 = 4 := by
          have : n % 3 = 2 := h₁
          have : (2 ^ n) % 7 = (2 ^ 2) % 7 := by
            rw [← Nat.div_add_mod n 3]
            simp [pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod, this]
            <;> norm_num <;> simp [Nat.pow_mod] <;> decide
          norm_num at this ⊢
          <;> omega
        have h₃ : (2 ^ n - 1) % 7 = 3 := by
          have : (2 ^ n) % 7 = 4 := h₂
          have : 2 ^ n ≥ 1 := Nat.one_le_pow _ _ (by omega)
          have : (2 ^ n - 1) % 7 = ((2 ^ n) % 7 - 1) % 7 := by
            rw [← Nat.mod_add_div (2 ^ n) 7]
            simp [Nat.sub_eq_zero_iff_le, Nat.add_mod, Nat.mul_mod, this]
            <;> omega
          omega
        have : (2 ^ n - 1) % 7 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
        omega
    omega
  · -- Backward direction: if 3 | n, then 7 | 2^n - 1
    intro h
    obtain ⟨k, rfl⟩ := h
    have : (2 ^ (3 * k)) % 7 = 1 := by
      rw [pow_mul]
      simp [Nat.pow_mod, Nat.mul_mod]
      induction k <;> simp_all [pow_succ, Nat.mul_mod, Nat.pow_mod] <;> norm_num
      <;> omega
    have : 7 ∣ 2 ^ (3 * k) - 1 := by
      have h₁ : 2 ^ (3 * k) ≥ 1 := Nat.one_le_pow _ _ (by omega)
      have h₂ : (2 ^ (3 * k) - 1) % 7 = 0 := by
        have : (2 ^ (3 * k)) % 7 = 1 := this
        omega
      exact Nat.dvd_of_mod_eq_zero h₂
    exact this

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  intro h
  have : (2 ^ n + 1) % 7 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
  have : (2 ^ n) % 7 = 1 ∨ (2 ^ n) % 7 = 2 ∨ (2 ^ n) % 7 = 4 := by
    have : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases this with (h₁ | h₁ | h₁)
    · -- Case n ≡ 0 (mod 3)
      have : (2 ^ n) % 7 = 1 := by
        have : n % 3 = 0 := h₁
        have : (2 ^ n) % 7 = 1 := by
          rw [← Nat.div_add_mod n 3]
          simp [pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod, this]
          <;> norm_num <;> simp [Nat.pow_mod] <;> decide
        exact this
      exact Or.inl this
    · -- Case n ≡ 1 (mod 3)
      have : (2 ^ n) % 7 = 2 := by
        have : n % 3 = 1 := h₁
        have : (2 ^ n) % 7 = 2 := by
          rw [← Nat.div_add_mod n 3]
          simp [pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod, this]
          <;> norm_num <;> simp [Nat.pow_mod] <;> decide
        exact this
      exact Or.inr (Or.inl this)
    · -- Case n ≡ 2 (mod 3)
      have : (2 ^ n) % 7 = 4 := by
        have : n % 3 = 2 := h₁
        have : (2 ^ n) % 7 = 4 := by
          rw [← Nat.div_add_mod n 3]
          simp [pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod, this]
          <;> norm_num <;> simp [Nat.pow_mod] <;> decide
        exact this
      exact Or.inr (Or.inr this)
  rcases this with (h₁ | h₁ | h₁)
  · -- Case (2^n) % 7 = 1
    have : (2 ^ n + 1) % 7 = 2 := by
      omega
    omega
  · -- Case (2^n) % 7 = 2
    have : (2 ^ n + 1) % 7 = 3 := by
      omega
    omega
  · -- Case (2^n) % 7 = 4
    have : (2 ^ n + 1) % 7 = 5 := by
      omega
    omega
