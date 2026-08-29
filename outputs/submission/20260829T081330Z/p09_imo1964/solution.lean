import Mathlib

-- Helper lemmas for modular arithmetic of 2^n mod 7
lemma pow_two_mod_seven_period (n k : ℕ) :
    (2 ^ (3 * k + n)) % 7 = (2 ^ n) % 7 := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      (2 ^ (3 * (k + 1) + n)) % 7 
        = (2 ^ (3 * k + n + 3)) % 7 := by ring_nf
      _ = (2 ^ (3 * k + n) * 2 ^ 3) % 7 := by rw [pow_add]
      _ = ((2 ^ (3 * k + n)) % 7 * (2 ^ 3 % 7)) % 7 := by simp [Nat.mul_mod]
      _ = ((2 ^ n % 7) * 1) % 7 := by rw [ih]; norm_num
      _ = (2 ^ n) % 7 := by simp

lemma pow_two_mod_seven_zero_case (k : ℕ) : (2 ^ (3 * k)) % 7 = 1 := by
  calc
    (2 ^ (3 * k)) % 7 
      = ((2 ^ 3) ^ k) % 7 := by rw [pow_mul]
    _ = (8 ^ k) % 7 := by norm_num
    _ = 1 := by
      have h : ∀ m : ℕ, (8 ^ m) % 7 = 1 := by
        intro m
        induction m with
        | zero => simp
        | succ m ih =>
          simp [Nat.pow_succ, Nat.mul_mod, ih]
          <;> norm_num
      exact h k

lemma pow_two_mod_seven_one_case (k : ℕ) : (2 ^ (3 * k + 1)) % 7 = 2 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    calc
      (2 ^ (3 * (k + 1) + 1)) % 7 
        = (2 ^ (3 * k + 4)) % 7 := by ring_nf
      _ = (2 ^ (3 * k + 1 + 3)) % 7 := by ring_nf
      _ = (2 ^ (3 * k + 1) * 2 ^ 3) % 7 := by rw [pow_add]
      _ = ((2 ^ (3 * k + 1)) % 7 * (2 ^ 3 % 7)) % 7 := by simp [Nat.mul_mod]
      _ = (2 * 1) % 7 := by rw [ih]; norm_num
      _ = 2 := by norm_num

lemma pow_two_mod_seven_two_case (k : ℕ) : (2 ^ (3 * k + 2)) % 7 = 4 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    calc
      (2 ^ (3 * (k + 1) + 2)) % 7 
        = (2 ^ (3 * k + 5)) % 7 := by ring_nf
      _ = (2 ^ (3 * k + 2 + 3)) % 7 := by ring_nf
      _ = (2 ^ (3 * k + 2) * 2 ^ 3) % 7 := by rw [pow_add]
      _ = ((2 ^ (3 * k + 2)) % 7 * (2 ^ 3 % 7)) % 7 := by simp [Nat.mul_mod]
      _ = (4 * 1) % 7 := by rw [ih]; norm_num
      _ = 4 := by norm_num

-- Connection between divisibility and modular arithmetic
lemma dvd_of_pow_mod_eq_one (n : ℕ) (h : 2 ^ n % 7 = 1) : 7 ∣ 2 ^ n - 1 := by
  omega

lemma plus_one_dvd_implies_mod_six (n : ℕ) (h : 7 ∣ 2 ^ n + 1) : 2 ^ n % 7 = 6 := by
  omega

-- Key lemma: 2^n mod 7 is never 6
lemma pow_two_mod_never_six (n : ℕ) : 2 ^ n % 7 ≠ 6 := by
  have h₀ : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h₀ with (h₀ | h₀ | h₀)
  · -- Case n % 3 = 0
    have : ∃ k : ℕ, n = 3 * k := by
      use n / 3
      have h₁ := Nat.mod_add_div n 3
      omega
    rcases this with ⟨k, rfl⟩
    rw [pow_two_mod_seven_zero_case]
    norm_num
  · -- Case n % 3 = 1
    have : ∃ k : ℕ, n = 3 * k + 1 := by
      use n / 3
      have h₁ := Nat.mod_add_div n 3
      omega
    rcases this with ⟨k, rfl⟩
    rw [pow_two_mod_seven_one_case]
    norm_num
  · -- Case n % 3 = 2
    have : ∃ k : ℕ, n = 3 * k + 2 := by
      use n / 3
      have h₁ := Nat.mod_add_div n 3
      omega
    rcases this with ⟨k, rfl⟩
    rw [pow_two_mod_seven_two_case]
    norm_num

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  constructor
  · -- Forward direction: 7 ∣ 2^n - 1 → 3 ∣ n
    intro h
    have h_mod : 2 ^ n % 7 = 1 := by
      have h' : 7 ∣ 2 ^ n - 1 := h
      have : 2 ^ n ≥ 1 := by
        apply Nat.one_le_pow
        omega
      omega
    -- Use contrapositive: if 3 ∤ n, then 2^n % 7 ≠ 1
    by_contra h_not_3div
    have h_mod_neq : 2 ^ n % 7 ≠ 1 := by
      have h₀ : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases h₀ with (h₀ | h₀ | h₀)
      · -- This case contradicts h_not_3div
        exfalso
        apply h_not_3div
        use n / 3
        have h₁ := Nat.mod_add_div n 3
        omega
      · -- Case n % 3 = 1
        have : ∃ k : ℕ, n = 3 * k + 1 := by
          use n / 3
          have h₁ := Nat.mod_add_div n 3
          omega
        rcases this with ⟨k, rfl⟩
        rw [pow_two_mod_seven_one_case]
        norm_num
      · -- Case n % 3 = 2
        have : ∃ k : ℕ, n = 3 * k + 2 := by
          use n / 3
          have h₁ := Nat.mod_add_div n 3
          omega
        rcases this with ⟨k, rfl⟩
        rw [pow_two_mod_seven_two_case]
        norm_num
    contradiction
  · -- Backward direction: 3 ∣ n → 7 ∣ 2^n - 1
    intro h
    have : ∃ k : ℕ, n = 3 * k := by
      obtain ⟨k, hk⟩ := h
      exact ⟨k, hk⟩
    rcases this with ⟨k, rfl⟩
    have h_mod : (2 ^ (3 * k)) % 7 = 1 := pow_two_mod_seven_zero_case k
    exact dvd_of_pow_mod_eq_one (3 * k) h_mod

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  intro h
  have h_mod : 2 ^ n % 7 = 6 := plus_one_dvd_implies_mod_six n h
  have h_never_six : 2 ^ n % 7 ≠ 6 := pow_two_mod_never_six n
  contradiction
