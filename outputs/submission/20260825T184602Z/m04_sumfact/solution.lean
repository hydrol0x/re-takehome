import Mathlib

/-- `∑_{i=1}^{n} i * i! = (n + 1)! - 1` for every natural number `n`. -/
theorem m04_sumfact (n : ℕ) :
    ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) =
      Nat.factorial (n + 1) - 1 := by
  have h_fact_ge_one : ∀ k : ℕ, Nat.factorial k ≥ 1 := by
    intro k
    exact Nat.succ_le_of_lt (Nat.factorial_pos k)
  
  induction n with
  | zero =>
    simp [Finset.sum_range_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h_fact_succ_pos : Nat.factorial (n + 1) ≥ 1 := h_fact_ge_one (n + 1)
    have h_fact_succ_add_one_pos : Nat.factorial (n + 2) ≥ 1 := h_fact_ge_one (n + 2)
    simp [Nat.factorial_succ, Nat.mul_comm, Nat.mul_assoc, Nat.mul_left_comm] at *
    rw [add_assoc]
    ring_nf at *
    omega
