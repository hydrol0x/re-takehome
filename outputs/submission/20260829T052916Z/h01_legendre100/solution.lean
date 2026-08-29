import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.IntervalCases

/-- The largest `k` such that `3 ^ k ∣ 100!`. Must be a numeric literal. -/
abbrev h01_answer : ℕ := 48

/-- `h01_answer` is the greatest `k` with `3 ^ k` dividing `100!`. -/
theorem h01_legendre100 :
    IsGreatest {k : ℕ | 3 ^ k ∣ Nat.factorial 100} h01_answer := by
  constructor
  · -- Part 1: Show that 3^48 divides 100!
    -- We compute v_3(100!) = floor(100/3) + floor(100/9) + floor(100/27) + floor(100/81) = 33 + 11 + 3 + 1 = 48
    have h : 3 ^ 48 ∣ Nat.factorial 100 := by
      norm_num [Nat.dvd_iff_mod_eq_zero, Nat.factorial]
      <;>
      decide
    exact h
  · -- Part 2: Show that for any k > 48, 3^k does not divide 100!
    intro k hk
    rw [Set.mem_setOf] at hk
    -- If 3^k divides 100!, then k ≤ 48
    have h : k ≤ 48 := by
      by_contra h'
      -- If k > 48, we get a contradiction
      have h'' : k ≥ 49 := by omega
      -- Use the fact that v_3(100!) = 48, so 3^49 cannot divide 100!
      have h''' : ¬(3 ^ k ∣ Nat.factorial 100) := by
        intro h_div
        -- If 3^k divides 100! for k ≥ 49, then 3^49 divides 100!
        have h₄₉ : 3 ^ 49 ∣ Nat.factorial 100 := by
          have h_k_ge_49 : k ≥ 49 := by omega
          have : 3 ^ 49 ∣ 3 ^ k := by
            apply pow_dvd_pow _ (by omega)
          exact dvd_trans this h_div
        -- But we can verify that 3^49 does not divide 100!
        norm_num [Nat.dvd_iff_mod_eq_zero, Nat.factorial] at h₄₉
        <;>
        (try omega) <;>
        (try {
          -- Calculate the actual valuation
          have h_val : (Nat.factorial 100).mod 3 ^ 49 ≠ 0 := by
            norm_num [Nat.factorial]
            <;>
            decide
          omega
        })
      exact h''' hk
    exact h
