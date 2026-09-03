import Mathlib

/-- Legendre count: the exponent of `3` in `100!` is `48`. -/
lemma h01_factorization : (Nat.factorial 100).factorization 3 = 48 := by
  have hp : Nat.Prime 3 := by norm_num
  have hb : Nat.log 3 100 < 5 := by norm_num
  rw [Nat.factorization_factorial hp hb]
  decide

/-- Divisibility of `100!` by powers of `3`, reduced to the Legendre count. -/
lemma h01_dvd_iff (k : ℕ) : 3 ^ k ∣ Nat.factorial 100 ↔ k ≤ 48 := by
  rw [Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) (Nat.factorial_ne_zero 100),
    h01_factorization]

/-- The largest `k` such that `3 ^ k ∣ 100!`. Must be a numeric literal. -/
abbrev h01_answer : ℕ := 48

/-- `h01_answer` is the greatest `k` with `3 ^ k` dividing `100!`. -/
theorem h01_legendre100 :
    IsGreatest {k : ℕ | 3 ^ k ∣ Nat.factorial 100} h01_answer := by
  constructor
  · show 3 ^ 48 ∣ Nat.factorial 100
    exact (h01_dvd_iff 48).mpr le_rfl
  · intro k hk
    show k ≤ 48
    exact (h01_dvd_iff k).mp hk
