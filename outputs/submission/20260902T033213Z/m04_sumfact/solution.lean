import Mathlib

/-- `∑_{i=1}^{n} i * i! = (n + 1)! - 1` for every natural number `n`. -/
theorem m04_sumfact (n : ℕ) :
    ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) =
      Nat.factorial (n + 1) - 1 := by
  induction' n with n ih
  · -- Base case: n = 0
    simp [Nat.factorial]
  · -- Inductive step: assume true for n, prove for n + 1
    rw [Finset.sum_range_succ]
    rw [ih]
    have h_fact_pos : 1 ≤ Nat.factorial (n + 1) := Nat.succ_le_of_lt (Nat.factorial_pos _)
    simp [Nat.factorial, Nat.mul_sub_left_distrib, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at *
    ring_nf at *
    omega
