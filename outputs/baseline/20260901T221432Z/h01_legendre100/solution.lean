import Mathlib

open Nat

/-- The largest `k` such that `3 ^ k ∣ 100!`. Must be a numeric literal. -/
abbrev h01_answer : ℕ := 48

/-- `h01_answer` is the greatest `k` with `3 ^ k` dividing `100!`. -/
theorem h01_legendre100 :
    IsGreatest {k : ℕ | 3 ^ k ∣ Nat.factorial 100} h01_answer := by
  -- 3 is prime
  have hp : Nat.Prime 3 := by norm_num
  -- valuation of 100! at the prime 3
  have hval : Nat.valuation (Nat.factorial 100) 3 = 48 := by
    have h := Nat.valuation_factorial (p := 3) (hp := hp) (n := 100)
    -- the right‑hand side evaluates to 48
    simpa using h
  -- 3^48 divides 100!
  have hdiv : 3 ^ 48 ∣ Nat.factorial 100 := by
    have : (48 : ℕ) ≤ Nat.valuation (Nat.factorial 100) 3 := by
      simpa [hval] using (le_rfl : (48 : ℕ) ≤ 48)
    exact (Nat.pow_dvd_iff_le_valuation).mpr this
  refine IsGreatest.mk ?mem ?bound
  · exact hdiv
  · intro k hk
    have hkle : k ≤ Nat.valuation (Nat.factorial 100) 3 :=
      (Nat.pow_dvd_iff_le_valuation).mp hk
    simpa [hval] using hkle
