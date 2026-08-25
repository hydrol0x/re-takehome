import Mathlib

/-- `∑_{i=1}^{n} i * i! = (n + 1)! - 1` for every natural number `n`. -/
theorem m04_sumfact (n : ℕ) :
    ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) =
      Nat.factorial (n + 1) - 1 := by
  induction' n with n ih
  · -- Base case: n = 0
    simp [Nat.factorial]
  · -- Inductive step
    rw [Finset.sum_range_succ, ih]
    have h₁ : Nat.factorial (n + 1) ≥ 1 := by
      apply Nat.succ_le_of_lt
      exact Nat.factorial_pos _
    have h₂ : Nat.factorial (n + 2) = (n + 2) * Nat.factorial (n + 1) := by
      simp [Nat.factorial, mul_comm]
      <;> ring_nf
    rw [h₂]
    ring_nf at *
    omega
