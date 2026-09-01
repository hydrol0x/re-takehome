import Mathlib

open Nat

/-- The largest `k` such that `3 ^ k ∣ 100!`. Must be a numeric literal. -/
abbrev h01_answer : ℕ := 48

/-- `h01_answer` is the greatest `k` with `3 ^ k` dividing `100!`. -/
theorem h01_legendre100 :
    IsGreatest {k : ℕ | 3 ^ k ∣ Nat.factorial 100} h01_answer := by
  -- the prime we are interested in
  have hp : Nat.Prime 3 := by norm_num
  -- Legendre's formula for the exponent of 3 in 100!
  have hleg : Nat.legendre 3 100 = 48 := by
    norm_num [Nat.legendre]
  refine ⟨?mem, ?ub⟩
  · -- membership: `3 ^ 48 ∣ 100!`
    have : (3 ^ 48) ∣ Nat.factorial 100 :=
      (Nat.prime_pow_dvd_factorial_iff (p := 3) (n := 100) (k := 48) hp).mpr
        (by
          -- we need `48 ≤ Nat.legendre 3 100`
          have : (48 : ℕ) ≤ Nat.legendre 3 100 := by
            simpa [hleg] using (le_rfl : (48 : ℕ) ≤ 48)
          exact this)
    exact this
  · -- upper bound: any `k` with `3 ^ k ∣ 100!` satisfies `k ≤ 48`
    intro k hk
    have hle : k ≤ Nat.legendre 3 100 :=
      (Nat.prime_pow_dvd_factorial_iff (p := 3) (n := 100) (k := k) hp).mp hk
    simpa [hleg] using hle
