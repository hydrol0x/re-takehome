import Mathlib.Tactic
import Mathlib.Data.Nat.ModEq
import Mathlib.NumberTheory.Divisors

/-- Powers of 2 modulo 7 follow a pattern: 1, 2, 4 repeating every 3 steps. -/
lemma pow_two_mod_seven (k : ℕ) : 2 ^ k % 7 = if k % 3 = 0 then 1 else if k % 3 = 1 then 2 else 4 := by
  have h : ∀ k : ℕ, 2 ^ k % 7 = if k % 3 = 0 then 1 else if k % 3 = 1 then 2 else 4 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      simp [Nat.mul_mod, Nat.add_mod, ih]
      split_ifs <;> norm_num <;> omega
  exact h k

theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  constructor
  · intro h
    have h₁ : 2 ^ n % 7 = 1 := by
      have h₂ : (2 ^ n - 1) % 7 = 0 := by
        rw [← Nat.mod_eq_zero_of_dvd h]
      have h₃ : 2 ^ n ≥ 1 := by
        apply Nat.one_le_pow
        linarith
      have h₄ : (2 ^ n - 1) % 7 = (2 ^ n % 7 - 1) % 7 := by
        rw [← Nat.sub_sub_self (by omega)]
        simp [Nat.mod_add_div]
      rw [h₂] at h₄
      have h₅ : (2 ^ n % 7 - 1) % 7 = 0 := by simpa using h₄
      have h₆ : 2 ^ n % 7 = 1 := by
        have h₇ : 2 ^ n % 7 < 7 := Nat.mod_lt _ (by norm_num)
        interval_cases 2 ^ n % 7 <;> norm_num at h₅ ⊢ <;> omega
      exact h₆
    have h₂ : n % 3 = 0 := by
      rw [pow_two_mod_seven] at h₁
      split_ifs at h₁ <;> try contradiction <;> omega
    exact Nat.dvd_of_mod_eq_zero h₂
  · intro h
    have h₁ : n % 3 = 0 := Nat.mod_eq_zero_of_dvd h
    have h₂ : 2 ^ n % 7 = 1 := by
      rw [pow_two_mod_seven]
      simp [h₁]
    have h₃ : (2 ^ n - 1) % 7 = 0 := by
      have h₄ : 2 ^ n ≥ 1 := by
        apply Nat.one_le_pow
        linarith
      have h₅ : (2 ^ n - 1) % 7 = (2 ^ n % 7 - 1) % 7 := by
        rw [← Nat.sub_sub_self (by omega)]
        simp [Nat.mod_add_div]
      rw [h₅, h₂]
      norm_num
    exact Nat.mod_eq_zero_of_dvd h₃

theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  intro h
  have h₁ : (2 ^ n + 1) % 7 = 0 := by
    rw [← Nat.mod_eq_zero_of_dvd h]
  have h₂ : 2 ^ n % 7 = 6 := by
    have h₃ : (2 ^ n % 7 + 1) % 7 = 0 := by
      rw [← Nat.mod_add_mod] at h₁
      omega
    have h₄ : 2 ^ n % 7 < 7 := Nat.mod_lt _ (by norm_num)
    interval_cases 2 ^ n % 7 <;> norm_num at h₃ ⊢ <;> omega
  have h₃ : 2 ^ n % 7 = if n % 3 = 0 then 1 else if n % 3 = 1 then 2 else 4 := pow_two_mod_seven n
  rw [h₃] at h₂
  split_ifs at h₂ <;> norm_num at h₂ <;> omega
