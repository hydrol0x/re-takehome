import Mathlib.Data.Nat.Factorization
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Factorial
import Mathlib.Tactic

open Nat

/-- The largest `k` such that `3 ^ k ∣ 100!`. Must be a numeric literal. -/
abbrev h01_answer : ℕ := 48

/-- `h01_answer` is the greatest `k` with `3 ^ k` dividing `100!`. -/
theorem h01_legendre100 :
    IsGreatest {k : ℕ | 3 ^ k ∣ Nat.factorial 100} h01_answer := by
  have hprime : Nat.Prime 3 := by
    decide
  -- compute the 3‑adic valuation of `100!`
  have hval : Nat.valuation 3 (Nat.factorial 100) = 48 := by
    simpa using (Nat.valuation_factorial (p := 3) (n := 100))
  refine ⟨?mem, ?bound⟩
  · -- `3 ^ 48` divides `100!`
    have : (48 : ℕ) ≤ Nat.valuation 3 (Nat.factorial 100) := by
      simpa [hval]
    exact (Nat.pow_dvd_iff_le_valuation (p := 3) (n := Nat.factorial 100)).mpr this
  · intro k hk
    have hk' :=
      (Nat.pow_dvd_iff_le_valuation (p := 3) (n := Nat.factorial 100)).mp hk
    simpa [hval] using hk'
