import Mathlib.NumberTheory.ModularArithmetic
import Mathlib.Tactic

/-- (a): `23 ∣ 2 ^ n - 1` iff `11 ∣ n`, for positive `n`. -/
theorem h02_a (n : ℕ) (hn : 0 < n) : 23 ∣ 2 ^ n - 1 ↔ 11 ∣ n := by
  constructor
  · -- Forward direction: if 23 ∣ 2^n - 1, then 11 ∣ n
    intro h
    have h_mod : 2 ^ n % 23 = 1 := by
      rw [Nat.dvd_iff_mod_eq_zero] at h
      omega
    -- Show that the order of 2 mod 23 is 11
    have h_order : ∀ k : ℕ, 0 < k → 2 ^ k % 23 = 1 → 11 ∣ k := by
      intro k hk h_k_mod
      -- Check all possible remainders mod 11
      have h_rem : k % 11 = 0 := by
        have : k % 11 < 11 := Nat.mod_lt k (by norm_num)
        interval_cases k % 11 <;> simp_all [pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
        <;> try contradiction
        <;> omega
      omega
    exact h_order n hn h_mod
  · -- Backward direction: if 11 ∣ n, then 23 ∣ 2^n - 1
    intro h
    have h_mod : 2 ^ n % 23 = 1 := by
      obtain ⟨k, rfl⟩ := h
      have : ∀ m : ℕ, 2 ^ (11 * m) % 23 = 1 := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
          simp [pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod, ih]
          <;> norm_num
      exact this k
    rw [← Nat.mod_add_div (2 ^ n) 23]
    simp [h_mod]
    <;> omega

/-- (b): no positive `n` has `23 ∣ 2 ^ n + 1`. -/
theorem h02_b (n : ℕ) (hn : 0 < n) : ¬23 ∣ 2 ^ n + 1 := by
  intro h
  have h_mod : 2 ^ n % 23 = 22 := by
    rw [Nat.dvd_iff_mod_eq_zero] at h
    have : (2 ^ n + 1) % 23 = 0 := h
    have : 2 ^ n % 23 = 22 := by
      omega
    exact this
  -- If 2^n ≡ -1 (mod 23), then 2^(2n) ≡ 1 (mod 23)
  have h_sq : 2 ^ (2 * n) % 23 = 1 := by
    calc
      2 ^ (2 * n) % 23 = (2 ^ n * 2 ^ n) % 23 := by ring_nf
      _ = ((2 ^ n % 23) * (2 ^ n % 23)) % 23 := by simp [Nat.mul_mod]
      _ = (22 * 22) % 23 := by rw [h_mod]
      _ = 1 := by norm_num
  -- From part (a), 2^(2n) ≡ 1 (mod 23) implies 11 ∣ 2n
  have h_11_dvd_2n : 11 ∣ 2 * n := by
    have h_order : ∀ k : ℕ, 0 < k → 2 ^ k % 23 = 1 → 11 ∣ k := by
      intro k hk h_k_mod
      have h_rem : k % 11 = 0 := by
        have : k % 11 < 11 := Nat.mod_lt k (by norm_num)
        interval_cases k % 11 <;> simp_all [pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
        <;> try contradiction
        <;> omega
      omega
    exact h_order (2 * n) (by linarith) h_sq
  -- Since 11 is prime and 11 ∤ 2, we must have 11 ∣ n
  have h_11_dvd_n : 11 ∣ n := by
    have : 11 ∣ 2 * n := h_11_dvd_2n
    have : 11 ∣ n := by
      apply Nat.Prime.dvd_of_dvd_mul_left (by norm_num : Nat.Prime 11)
      exact this
    exact this
  -- But if 11 ∣ n, then 2^n ≡ 1 (mod 23), contradicting 2^n ≡ 22 (mod 23)
  have h_contra : False := by
    have h_mod_n : 2 ^ n % 23 = 1 := by
      have h_order : ∀ k : ℕ, 0 < k → 11 ∣ k → 2 ^ k % 23 = 1 := by
        intro k hk h_dvd
        obtain ⟨m, rfl⟩ := h_dvd
        have : ∀ m : ℕ, 2 ^ (11 * m) % 23 = 1 := by
          intro m
          induction m with
          | zero => simp
          | succ m ih =>
            simp [pow_add, pow_mul, Nat.pow_mod, Nat.mul_mod, ih]
            <;> norm_num
        exact this m
      exact h_order n hn h_11_dvd_n
    omega
  exact h_contra
