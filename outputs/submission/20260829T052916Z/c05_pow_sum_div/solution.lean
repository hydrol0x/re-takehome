import Mathlib

/-- Helper: 2025 ≡ 1 (mod 4) -/
lemma two_zero_two_five_mod_four : 2025 % 4 = 1 := by decide

-- Compute 2^2025 mod 5 using the cycle of powers of 2 mod 5
lemma two_pow_2025_mod_five : (2 ^ 2025) % 5 = 2 := by
  have h_cycle : ∀ n : ℕ, (2 ^ n) % 5 = 
    if n % 4 = 0 then 1
    else if n % 4 = 1 then 2
    else if n % 4 = 2 then 4
    else 3 := by
    intro n
    have h₁ : ∃ q r : ℕ, n = 4 * q + r ∧ r < 4 := by
      use n / 4, n % 4
      constructor
      · rw [Nat.div_add_mod]
      · exact Nat.mod_lt _ (by decide)
    rcases h₁ with ⟨q, r, rfl, hr⟩
    have h₂ : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases h₂ with (rfl | rfl | rfl | rfl) <;>
      simp [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, Nat.add_mod] <;>
      norm_num <;>
      omega
  rw [h_cycle 2025]
  simp [two_zero_two_five_mod_four]
  <;> decide

-- Compute 3^2025 mod 5 using the cycle of powers of 3 mod 5
lemma three_pow_2025_mod_five : (3 ^ 2025) % 5 = 3 := by
  have h_cycle : ∀ n : ℕ, (3 ^ n) % 5 = 
    if n % 4 = 0 then 1
    else if n % 4 = 1 then 3
    else if n % 4 = 2 then 4
    else 2 := by
    intro n
    have h₁ : ∃ q r : ℕ, n = 4 * q + r ∧ r < 4 := by
      use n / 4, n % 4
      constructor
      · rw [Nat.div_add_mod]
      · exact Nat.mod_lt _ (by decide)
    rcases h₁ with ⟨q, r, rfl, hr⟩
    have h₂ : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases h₂ with (rfl | rfl | rfl | rfl) <;>
      simp [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod, Nat.add_mod] <;>
      norm_num <;>
      omega
  rw [h_cycle 2025]
  simp [two_zero_two_five_mod_four]
  <;> decide

-- Sum mod 5 equals 0
lemma sum_mod_five : (2 ^ 2025 + 3 ^ 2025) % 5 = 0 := by
  rw [Nat.add_mod]
  rw [two_pow_2025_mod_five, three_pow_2025_mod_five]
  <;> norm_num

/-- `5` divides `2 ^ 2025 + 3 ^ 2025`. -/
theorem c05_pow_sum_div : 5 ∣ 2 ^ 2025 + 3 ^ 2025 := by
  rw [Nat.dvd_iff_mod_eq_zero]
  rw [sum_mod_five]
