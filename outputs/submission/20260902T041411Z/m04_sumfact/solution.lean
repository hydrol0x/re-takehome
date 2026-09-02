import Mathlib

/-- `∑_{i=1}^{n} i * i! = (n + 1)! - 1` for every natural number `n`. -/
theorem m04_sumfact (n : ℕ) :
    ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) =
      Nat.factorial (n + 1) - 1 := by
  have h_fact_pos : ∀ k : ℕ, 0 < Nat.factorial k := by
    intro k
    exact Nat.factorial_pos k
  
  induction' n with n ih
  · -- Base case: n = 0
    simp [Finset.sum_range_zero]
  · -- Inductive step
    rw [Finset.sum_range_succ, ih]
    have h_fact_n_plus_1_pos : 0 < Nat.factorial (n + 1) := h_fact_pos (n + 1)
    have h_fact_n_plus_2_pos : 0 < Nat.factorial (n + 2) := h_fact_pos (n + 2)
    have h_le : 1 ≤ Nat.factorial (n + 1) := by
      have := h_fact_pos (n + 1)
      omega
    -- Simplify the equation using algebraic manipulation
    simp_all [Nat.factorial_succ, Nat.mul_sub_left_distrib, Nat.add_assoc]
    -- Use ring to simplify and then omega for the arithmetic
    ring_nf at *
    omega
