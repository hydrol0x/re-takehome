import Mathlib

/-- `∑_{i=1}^{n} i * i! = (n + 1)! - 1` for every natural number `n`. -/
theorem m04_sumfact (n : ℕ) :
    ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) =
      Nat.factorial (n + 1) - 1 := by
  induction' n with n ih
  · -- Base case: n = 0
    simp [Nat.factorial]
  · -- Inductive step: assume true for n, prove for n + 1
    rw [Finset.sum_range_succ, ih]
    have h_fact_pos : Nat.factorial (n + 1) ≥ 1 := by
      apply Nat.succ_le_of_lt
      exact Nat.factorial_pos _
    have h_main : Nat.factorial (n + 1) - 1 + (n + 1) * Nat.factorial (n + 1) = 
                   Nat.factorial (n + 2) - 1 := by
      have h_fact_succ : Nat.factorial (n + 2) = (n + 2) * Nat.factorial (n + 1) := by
        simp [Nat.factorial]
      rw [h_fact_succ]
      have h_comm : (n + 1) * Nat.factorial (n + 1) + Nat.factorial (n + 1) = 
                     (n + 2) * Nat.factorial (n + 1) := by
        ring_nf
        <;> simp [Nat.mul_add, Nat.add_mul]
        <;> ring_nf
      have h_sub : Nat.factorial (n + 1) - 1 + ((n + 1) * Nat.factorial (n + 1)) = 
                    ((n + 1) * Nat.factorial (n + 1) + Nat.factorial (n + 1)) - 1 := by
        omega
      rw [h_sub, h_comm]
      <;> omega
    rw [h_main]
