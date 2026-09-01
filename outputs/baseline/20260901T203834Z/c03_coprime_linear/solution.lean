import Mathlib

/-- For every natural number `n`, the numbers `2 * n + 1` and `9 * n + 4` are coprime. -/
theorem c03_coprime_linear (n : ℕ) : Nat.gcd (2 * n + 1) (9 * n + 4) = 1 := by
  -- Prove the numbers are coprime via Bézout's identity.
  have hcop : Nat.coprime (2 * n + 1) (9 * n + 4) := by
    -- `9 * (2 * n + 1) - 2 * (9 * n + 4) = 1`
    refine (Nat.coprime_iff_exists_eq_mul_add).mpr ?_
    refine ⟨9, -2, ?_⟩
    ring
  simpa [Nat.coprime_iff_gcd_eq_one] using hcop
