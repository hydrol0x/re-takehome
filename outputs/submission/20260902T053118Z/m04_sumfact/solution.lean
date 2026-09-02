import Mathlib

/-- `∑_{i=1}^{n} i * i! = (n + 1)! - 1` for every natural number `n`. -/
theorem m04_sumfact (n : ℕ) :
    ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) =
      Nat.factorial (n + 1) - 1 := by
  have h_base : ∑ i ∈ Finset.range 0, (i + 1) * Nat.factorial (i + 1) = Nat.factorial (0 + 1) - 1 := by
    simp [Finset.sum_range_zero, Nat.factorial]
    <;> norm_num
  have h_ind : ∀ k : ℕ, (∑ i ∈ Finset.range k, (i + 1) * Nat.factorial (i + 1) = Nat.factorial (k + 1) - 1) →
    (∑ i ∈ Finset.range (k + 1), (i + 1) * Nat.factorial (i + 1) = Nat.factorial ((k + 1) + 1) - 1) := by
    intro k hk
    rw [Finset.sum_range_succ, hk]
    have h_fact_pos : Nat.factorial (k + 1) ≥ 1 := by
      apply Nat.one_le_of_lt
      exact Nat.factorial_pos (k + 1)
    have h_sub_eq : Nat.factorial (k + 1) - 1 + (k + 1) * Nat.factorial (k + 1) =
      (k + 2) * Nat.factorial (k + 1) - 1 := by
      have h1 : (k + 2) * Nat.factorial (k + 1) = (k + 1 + 1) * Nat.factorial (k + 1) := by ring
      have h2 : (k + 1 + 1) * Nat.factorial (k + 1) = (k + 1) * Nat.factorial (k + 1) + Nat.factorial (k + 1) := by ring
      have h3 : (k + 1) * Nat.factorial (k + 1) + Nat.factorial (k + 1) = Nat.factorial (k + 1) - 1 + (k + 1) * Nat.factorial (k + 1) + 1 := by
        have h4 : Nat.factorial (k + 1) - 1 + 1 = Nat.factorial (k + 1) := by
          rw [Nat.sub_add_cancel h_fact_pos]
        omega
      omega
    rw [h_sub_eq]
    have h_fact_succ : Nat.factorial (k + 2) = (k + 2) * Nat.factorial (k + 1) := by
      simp [Nat.factorial_succ, mul_comm]
      <;> ring_nf
    rw [← h_fact_succ]
    <;> simp [Nat.mul_add, add_mul]
    <;> ring_nf
    <;> omega
  induction' n with k ih
  · exact h_base
  · exact h_ind _ ih
