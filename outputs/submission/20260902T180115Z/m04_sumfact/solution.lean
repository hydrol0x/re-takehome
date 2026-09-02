import Mathlib

/-- `∑_{i=1}^{n} i * i! = (n + 1)! - 1` for every natural number `n`. -/
theorem m04_sumfact (n : ℕ) :
    ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) =
      Nat.factorial (n + 1) - 1 := by
  induction' n with n ih
  · simp
  rw [Finset.sum_range_succ, ih]
  have h : Nat.factorial (n + 1) ≥ 1 := by
    apply Nat.succ_le_of_lt
    exact Nat.factorial_pos _
  simp [Nat.factorial_succ, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc] at *
  ring_nf at *
  omega
