import Mathlib
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

open ZMod Units

/-- The order of 2 in the multiplicative group of ZMod 23 is 11. -/
lemma order_of_2_mod_23 : orderOf (Units.mk0 (2 : ZMod 23) (by decide)) = 11 := by
  have h_fact : Fact 11.Prime := ⟨by decide⟩
  apply orderOf_eq_prime h_fact
  · norm_num
  · norm_num

theorem h02_a (n : ℕ) (hn : 0 < n) : 23 ∣ 2 ^ n - 1 ↔ 11 ∣ n := by
  let u : Units (ZMod 23) := Units.mk0 (2 : ZMod 23) (by decide)
  have h_order : orderOf u = 11 := order_of_2_mod_23
  
  constructor
  · intro h
    -- 23 ∣ 2^n - 1 ↔ (2 : ZMod 23)^n = 1
    have h_mod : (u : ZMod 23) ^ n = 1 := by
      rw [← ZMod.natCast_zmod_eq_zero_iff_dvd]
      simp [h]
      <;> omega
    
    -- orderOf u ∣ n
    have h_dvd : orderOf u ∣ n := by
      apply pow_eq_one_iff_orderOf_dvd.mp
      exact h_mod
    
    rw [h_order] at h_dvd
    exact h_dvd
  
  · intro h
    -- 11 ∣ n → orderOf u ∣ n → u^n = 1
    have h_dvd : orderOf u ∣ n := by
      rw [h_order]
      exact h
    
    have h_mod : (u : ZMod 23) ^ n = 1 := by
      apply pow_eq_one_iff_orderOf_dvd.mpr
      exact h_dvd
    
    -- Convert to divisibility
    have h_div : 23 ∣ 2 ^ n - 1 := by
      rw [← ZMod.natCast_zmod_eq_zero_iff_dvd]
      simp [h_mod]
      <;> omega
    
    exact h_div

theorem h02_b (n : ℕ) (hn : 0 < n) : ¬23 ∣ 2 ^ n + 1 := by
  let u : Units (ZMod 23) := Units.mk0 (2 : ZMod 23) (by decide)
  have h_order : orderOf u = 11 := order_of_2_mod_23
  
  intro h
  -- 23 ∣ 2^n + 1 ↔ (2 : ZMod 23)^n = -1
  have h_mod : (u : ZMod 23) ^ n = -1 := by
    rw [← ZMod.natCast_zmod_eq_zero_iff_dvd]
    simp [h]
    <;> omega
  
  -- Square: (u^n)^2 = 1
  have h_sq : (u : ZMod 23) ^ (2 * n) = 1 := by
    calc
      (u : ZMod 23) ^ (2 * n) = ((u : ZMod 23) ^ n) ^ 2 := by
        rw [mul_comm, pow_mul]
      _ = (-1 : ZMod 23) ^ 2 := by rw [h_mod]
      _ = 1 := by norm_num
  
  -- orderOf u ∣ 2n
  have h_dvd : orderOf u ∣ 2 * n := by
    apply pow_eq_one_iff_orderOf_dvd.mp
    exact h_sq
  
  rw [h_order] at h_dvd
  -- 11 ∣ 2n → 11 ∣ n
  have h_n : 11 ∣ n := by
    have h11 : Nat.Prime 11 := by decide
    have h_not2 : ¬11 ∣ 2 := by decide
    exact (Nat.Prime.dvd_mul h11).mp h_dvd |>.resolve_left h_not2
  
  -- 11 ∣ n → u^n = 1
  have h_mod_1 : (u : ZMod 23) ^ n = 1 := by
    have h_dvd' : orderOf u ∣ n := by
      rw [h_order]
      exact h_n
    apply pow_eq_one_iff_orderOf_dvd.mpr
    exact h_dvd'
  
  -- Contradiction
  have h_contra : (1 : ZMod 23) = -1 := by
    rw [h_mod_1] at h_mod
    exact h_mod
  
  norm_num at h_contra
