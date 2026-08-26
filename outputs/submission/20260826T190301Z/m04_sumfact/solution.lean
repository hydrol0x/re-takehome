import Mathlib

/-- `∑_{i=1}^{n} i * i! = (n + 1)! - 1` for every natural number `n`. -/
theorem m04_sumfact (n : ℕ) :
    ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) =
      Nat.factorial (n + 1) - 1 := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h_fact_pos : Nat.factorial (n + 1) ≥ 1 := by
      apply Nat.succ_le_of_lt
      exact Nat.factorial_pos _
    have h_factorial_succ : Nat.factorial (n + 2) = (n + 2) * Nat.factorial (n + 1) := by
      rw [Nat.factorial_succ]
      <;> ring
    have h_main : Nat.factorial (n + 1) + (n + 1) * Nat.factorial (n + 1) = (n + 2) * Nat.factorial (n + 1) := by
      ring
    have h_subtract_ok : Nat.factorial (n + 1) - 1 + (n + 1) * Nat.factorial (n + 1) = 
                          Nat.factorial (n + 1) + (n + 1) * Nat.factorial (n + 1) - 1 := by
      have h_le : 1 ≤ Nat.factorial (n + 1) := h_fact_pos
      rw [← Nat.sub_add_cancel h_le]
      ring_nf
      <;> simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      <;> omega
    calc
      (Nat.factorial (n + 1) - 1) + (n + 1) * Nat.factorial (n + 1) =
        Nat.factorial (n + 1) + (n + 1) * Nat.factorial (n + 1) - 1 := by
        rw [h_subtract_ok]
      _ = (n + 2) * Nat.factorial (n + 1) - 1 := by
        rw [h_main]
      _ = Nat.factorial (n + 2) - 1 := by
        rw [h_factorial_succ]
