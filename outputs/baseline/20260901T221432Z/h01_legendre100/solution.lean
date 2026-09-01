import Mathlib
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Factorization

/-- The largest `k` such that `3 ^ k ∣ 100!`. Must be a numeric literal. -/
abbrev h01_answer : ℕ := 48

/-- `h01_answer` is the greatest `k` with `3 ^ k` dividing `100!`. -/
theorem h01_legendre100 :
    IsGreatest {k : ℕ | 3 ^ k ∣ Nat.factorial 100} h01_answer := by
  -- compute the 3‑adic valuation of `100!`
  have hval : Nat.valuation 3 (Nat.factorial 100) = 48 := by
    simpa using Nat.valuation_factorial (Nat.prime_three) 100
  refine ⟨?mem, ?bound⟩
  · -- `3 ^ 48` divides `100!`
    have hle : (48 : ℕ) ≤ Nat.valuation 3 (Nat.factorial 100) := by
      simpa [hval] using le_rfl
    exact (Nat.pow_dvd_iff_le_valuation (Nat.prime_three)).mpr hle
  · -- any exponent dividing `100!` is ≤ 48
    intro k hk
    have hk' : k ≤ Nat.valuation 3 (Nat.factorial 100) :=
      (Nat.pow_dvd_iff_le_valuation (Nat.prime_three)).mp hk
    simpa [hval] using hk'
