import Mathlib

/-- Powers of 2 mod 7 cycle with period 3: 2^0≡1, 2^1≡2, 2^2≡4, then repeat. -/
lemma pow_two_mod_seven_cycle (n : ℕ) :
  2 ^ n % 7 = if n % 3 = 0 then 1 else if n % 3 = 1 then 2 else 4 := by sorry

/-- For n > 0, 7 divides 2^n - 1 iff 3 divides n. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  have h₁ : 7 ∣ 2 ^ n - 1 ↔ 2 ^ n % 7 = 1 := by sorry
  have h₂ : 2 ^ n % 7 = 1 ↔ n % 3 = 0 := by sorry
  have h₃ : n % 3 = 0 ↔ 3 ∣ n := by omega
  exact (h₁.trans h₂).trans h₃

/-- No positive n exists where 7 divides 2^n + 1. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  have h₁ : ¬(2 ^ n + 1) % 7 = 0 := by
    rw [Nat.add_mod]
    rw [pow_two_mod_seven_cycle]
    have h_bound : n % 3 < 3 := Nat.mod_lt _ (by decide)
    interval_cases n % 3 <;> simp <;> norm_num
  have h₂ : 7 ∣ 2 ^ n + 1 ↔ (2 ^ n + 1) % 7 = 0 := by
    exact Nat.dvd_iff_mod_eq_zero
  intro h_dvd
  have h_mod_zero : (2 ^ n + 1) % 7 = 0 := h₂.mp h_dvd
  exact h₁ h_mod_zero
