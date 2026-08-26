import Mathlib

/-- `∑_{i=1}^{n} i * i! = (n + 1)! - 1` for every natural number `n`. -/
theorem m04_sumfact (n : ℕ) :
    ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) =
      Nat.factorial (n + 1) - 1 := by
  induction' n with n ih
  · -- Base case: n = 0
    simp [Finset.sum_range_zero]
  · -- Inductive step: assume true for n, prove for n + 1
    rw [Finset.sum_range_succ, ih]
    have h_fact_pos : Nat.factorial (n + 1) ≥ 1 := by
      apply Nat.succ_le_of_lt
      exact Nat.factorial_pos _
    have h_main : Nat.factorial (n + 1) - 1 + (n + 1) * Nat.factorial (n + 1) =
                   Nat.factorial (n + 2) - 1 := by
      have h1 : (n + 1) * Nat.factorial (n + 1) + Nat.factorial (n + 1) =
                (n + 2) * Nat.factorial (n + 1) := by
        ring_nf
        <;> simp [Nat.factorial_succ, mul_add, add_mul]
        <;> ring_nf
      calc
        Nat.factorial (n + 1) - 1 + (n + 1) * Nat.factorial (n + 1)
          = (n + 1) * Nat.factorial (n + 1) + Nat.factorial (n + 1) - 1 := by
            omega
        _ = (n + 2) * Nat.factorial (n + 1) - 1 := by
          rw [h1]
        _ = Nat.factorial (n + 2) - 1 := by
          rw [Nat.factorial_succ (n + 1)]
          <;> ring_nf
    rw [h_main]
