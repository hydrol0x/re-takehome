import Mathlib

/-- `∑_{i=1}^{n} i * i! = (n + 1)! - 1` for every natural number `n`. -/
theorem m04_sumfact (n : ℕ) :
    ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) =
      Nat.factorial (n + 1) - 1 := by
  induction n with
  | zero =>
    simp [Finset.sum_range_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    rw [ih]
    have h : Nat.factorial (n + 1) ≥ 1 := by
      apply Nat.succ_le_of_lt
      exact Nat.factorial_pos (n + 1)
    simp [Nat.factorial_succ, Nat.add_assoc] at *
    ring_nf at *
    <;> omega
