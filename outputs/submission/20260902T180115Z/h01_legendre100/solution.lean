import Mathlib

/-- The largest `k` such that `3 ^ k ∣ 100!`. Must be a numeric literal. -/
abbrev h01_answer : ℕ := 48

/-- `h01_answer` is the greatest `k` with `3 ^ k` dividing `100!`. -/
theorem h01_legendre100 :
    IsGreatest {k : ℕ | 3 ^ k ∣ Nat.factorial 100} h01_answer := by
  constructor
  · -- Show 3^48 divides 100!
    apply Nat.dvd_of_mod_eq_zero
    rw [Nat.factorial]
    norm_num [Nat.factorial, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    <;> rfl
  
  · -- Show that if 3^k divides 100!, then k ≤ 48
    intro k hk
    have : k ≤ 48 := by
      by_contra h
      -- Assume k > 48, so k ≥ 49
      have h' : k ≥ 49 := by omega
      -- We know 3^48 divides 100! but 3^49 doesn't
      -- The p-adic valuation of 100! for p=3 is: floor(100/3) + floor(100/9) + floor(100/27) + floor(100/81)
      -- = 33 + 11 + 3 + 1 = 48
      -- So 3^49 does not divide 100!
      have h_div : ¬(3 ^ 49 ∣ Nat.factorial 100) := by
        norm_num [Nat.factorial]
        <;> decide
      have h_k_ge_49 : 3 ^ k ∣ Nat.factorial 100 := hk
      have h_49 : 3 ^ 49 ∣ 3 ^ k := by
        apply pow_dvd_pow _
        omega
      have h_contra : 3 ^ 49 ∣ Nat.factorial 100 := dvd_trans h_49 h_k_ge_49
      exact h_div h_contra
    exact this
