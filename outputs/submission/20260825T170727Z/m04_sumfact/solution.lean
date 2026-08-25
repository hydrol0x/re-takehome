import Mathlib

/-- `∑_{i=1}^{n} i * i! = (n + 1)! - 1` for every natural number `n`. -/
theorem m04_sumfact (n : ℕ) :
    ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) =
      Nat.factorial (n + 1) - 1 := by
  have h_fact_pos : ∀ k : ℕ, k ≥ 1 → Nat.factorial k ≥ 1 := by
    intro k hk
    exact Nat.succ_le_of_lt (Nat.factorial_pos k)
  
  have h_main : ∀ n : ℕ, ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) = Nat.factorial (n + 1) - 1 := by
    intro n
    induction' n with n ih
    · -- Base case: n = 0
      simp [Nat.factorial]
    · -- Inductive step: assume for n, prove for n + 1
      rw [Finset.sum_range_succ, ih]
      have h_fact_n_plus_1_pos : Nat.factorial (n + 1) ≥ 1 := by
        apply h_fact_pos
        <;> omega
      have h_sub_valid : Nat.factorial (n + 1) - 1 + (n + 1) * Nat.factorial (n + 1) =
          (n + 1) * Nat.factorial (n + 1) + (Nat.factorial (n + 1) - 1) := by
        rw [add_comm]
        <;> omega
      calc
        Nat.factorial (n + 1) - 1 + (n + 1) * Nat.factorial (n + 1) =
            (n + 1) * Nat.factorial (n + 1) + (Nat.factorial (n + 1) - 1) := by rw [h_sub_valid]
        _ = (n + 1) * Nat.factorial (n + 1) + Nat.factorial (n + 1) - 1 := by
          have h_ge : Nat.factorial (n + 1) ≥ 1 := h_fact_n_plus_1_pos
          have h_bound : Nat.factorial (n + 1) - 1 ≤ Nat.factorial (n + 1) := by
            apply Nat.sub_le
          omega
        _ = (n + 1 + 1) * Nat.factorial (n + 1) - 1 := by
          have h_ge : Nat.factorial (n + 1) ≥ 1 := h_fact_n_plus_1_pos
          have h_bound : Nat.factorial (n + 1) - 1 ≤ Nat.factorial (n + 1) := by
            apply Nat.sub_le
          ring_nf
          <;> omega
        _ = Nat.factorial (n + 2) - 1 := by
          have h_factorial_succ : Nat.factorial (n + 2) = (n + 2) * Nat.factorial (n + 1) := by
            rw [Nat.factorial_succ, mul_comm]
            <;> ring
          rw [h_factorial_succ]
          <;> ring_nf
          <;> omega
  
  exact h_main n
