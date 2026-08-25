import Mathlib

/-- `∑_{i=1}^{n} i * i! = (n + 1)! - 1` for every natural number `n`. -/
theorem m04_sumfact (n : ℕ) :
    ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) =
      Nat.factorial (n + 1) - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Nat.factorial_succ (n + 1)]
    have h1 : 1 ≤ Nat.factorial (n + 1) :=
      Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h2 : 1 ≤ (n + 1 + 1) * Nat.factorial (n + 1) :=
      Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (Nat.factorial_ne_zero _))
    zify [h1, h2]
    ring
