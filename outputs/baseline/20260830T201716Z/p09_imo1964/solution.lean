import Mathlib.Tactic
import Mathlib.Data.Nat.ModEq

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  constructor
  · -- Forward direction: if 7 ∣ 2^n - 1, then 3 ∣ n
    intro h
    have h_mod : 2 ^ n % 7 = 1 := by
      have h' : (2 ^ n - 1) % 7 = 0 := Nat.mod_eq_zero_of_dvd h
      have h'' : 2 ^ n % 7 = 1 := by
        have : 2 ^ n ≥ 1 := by
          apply Nat.one_le_pow
          <;> omega
        omega
      exact h''
    -- Show that n must be divisible by 3 by checking cases mod 3
    have : n % 3 = 0 := by
      by_contra h_neq
      have h_cases : n % 3 = 1 ∨ n % 3 = 2 := by
        have : n % 3 ≠ 0 := h_neq
        have : n % 3 < 3 := Nat.mod_lt n (by norm_num)
        omega
      rcases h_cases with (h_cases | h_cases)
      · -- Case n ≡ 1 (mod 3)
        have : 2 ^ n % 7 = 2 := by
          have : ∃ k, n = 3 * k + 1 := by
            use n / 3
            have : n % 3 = 1 := h_cases
            omega
          rcases this with ⟨k, rfl⟩
          rw [pow_add, pow_mul]
          simp [Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
          <;> norm_num
          <;> ring_nf at *
          <;> omega
        omega
      · -- Case n ≡ 2 (mod 3)
        have : 2 ^ n % 7 = 4 := by
          have : ∃ k, n = 3 * k + 2 := by
            use n / 3
            have : n % 3 = 2 := h_cases
            omega
          rcases this with ⟨k, rfl⟩
          rw [pow_add, pow_mul]
          simp [Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
          <;> norm_num
          <;> ring_nf at *
          <;> omega
        omega
    omega
  · -- Backward direction: if 3 ∣ n, then 7 ∣ 2^n - 1
    intro h
    have h_mod : 2 ^ n % 7 = 1 := by
      have : ∃ k, n = 3 * k := by
        obtain ⟨k, hk⟩ := h
        exact ⟨k, by linarith⟩
      rcases this with ⟨k, rfl⟩
      rw [pow_mul]
      have : (2 ^ 3) ^ k % 7 = 1 := by
        have : 2 ^ 3 % 7 = 1 := by norm_num
        rw [← Nat.mod_add_div ((2 ^ 3) ^ k) 7]
        simp [this, Nat.pow_mod, Nat.mul_mod]
        <;> induction k <;> simp_all [pow_succ, Nat.mul_mod] <;> norm_num
        <;> omega
      omega
    have : (2 ^ n - 1) % 7 = 0 := by
      have : 2 ^ n ≥ 1 := by
        apply Nat.one_le_pow
        <;> omega
      omega
    exact Nat.dvd_of_mod_eq_zero this

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  intro h
  have h_mod : (2 ^ n + 1) % 7 = 0 := Nat.mod_eq_zero_of_dvd h
  have : 2 ^ n % 7 = 6 := by
    have : (2 ^ n + 1) % 7 = 0 := h_mod
    have : 2 ^ n % 7 < 7 := Nat.mod_lt _ (by norm_num)
    omega
  -- Check all possible remainders of 2^n mod 7
  have : 2 ^ n % 7 = 1 ∨ 2 ^ n % 7 = 2 ∨ 2 ^ n % 7 = 4 := by
    have : ∀ m : ℕ, 2 ^ m % 7 = 1 ∨ 2 ^ m % 7 = 2 ∨ 2 ^ m % 7 = 4 := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rcases ih with (ih | ih | ih)
        · -- 2^m ≡ 1 (mod 7)
          simp [ih, pow_succ, Nat.mul_mod]
          <;> norm_num
          <;> omega
        · -- 2^m ≡ 2 (mod 7)
          simp [ih, pow_succ, Nat.mul_mod]
          <;> norm_num
          <;> omega
        · -- 2^m ≡ 4 (mod 7)
          simp [ih, pow_succ, Nat.mul_mod]
          <;> norm_num
          <;> omega
    exact this n
  rcases this with (h1 | h2 | h3)
  · -- 2^n ≡ 1 (mod 7)
    omega
  · -- 2^n ≡ 2 (mod 7)
    omega
  · -- 2^n ≡ 4 (mod 7)
    omega
