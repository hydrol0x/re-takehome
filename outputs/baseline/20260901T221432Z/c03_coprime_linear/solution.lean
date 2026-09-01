import Mathlib

/-- For every natural number `n`, the numbers `2 * n + 1` and `9 * n + 4` are coprime. -/
theorem c03_coprime_linear (n : ℕ) : Nat.gcd (2 * n + 1) (9 * n + 4) = 1 := by
  -- rewrite the goal in terms of `Nat.Coprime`
  rw [← Nat.coprime_iff_gcd_eq_one]
  -- first we show that `2 * n + 1` is coprime with `n`
  have h₁ : Nat.Coprime (2 * n + 1) n := by
    have : (2 * n + 1) - 2 * n = 1 := by
      ring
    exact Nat.coprime_of_sub_eq_one this
  -- using the Euclidean algorithm we reduce the second number
  have h₂ : Nat.Coprime (2 * n + 1) (9 * n + 4) := by
    have : (9 * n + 4) - 4 * (2 * n + 1) = n := by
      ring
    -- `Nat.coprime_sub_left_iff` lets us replace the second argument by its
    -- difference with a multiple of the first argument.
    exact (Nat.coprime_sub_left_iff (2 * n + 1) (9 * n + 4) 4).mpr (by
      simpa [this] using h₁)
  exact h₂
