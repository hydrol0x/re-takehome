import Mathlib

/-- `∑_{i=1}^{n} i * i! = (n + 1)! - 1` for every natural number `n`. -/
theorem m04_sumfact (n : ℕ) :
    ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) =
      Nat.factorial (n + 1) - 1 := by
  have h_fact_pos : ∀ k : ℕ, Nat.factorial k ≥ 1 := by
    intro k
    exact Nat.succ_le_of_lt (Nat.factorial_pos k)
  
  induction' n with n ih
  · -- Base case: n = 0
    simp [Finset.sum_range_zero]
  · -- Inductive step
    rw [Finset.sum_range_succ, ih]
    have h₁ : Nat.factorial (n + 1) ≥ 1 := h_fact_pos (n + 1)
    have h₂ : Nat.factorial (n + 1) - 1 + (n + 1) * Nat.factorial (n + 1) = 
              Nat.factorial (n + 2) - 1 := by
      have h₃ : Nat.factorial (n + 2) = (n + 2) * Nat.factorial (n + 1) := by
        simp [Nat.factorial_succ]
        <;> ring
      rw [h₃]
      have h₄ : (n + 2) * Nat.factorial (n + 1) - 1 = 
                Nat.factorial (n + 1) - 1 + (n + 1) * Nat.factorial (n + 1) := by
        have h₅ : (n + 2) * Nat.factorial (n + 1) = 
                  Nat.factorial (n + 1) + (n + 1) * Nat.factorial (n + 1) := by
          ring
        rw [h₅]
        have h₆ : Nat.factorial (n + 1) ≥ 1 := h_fact_pos (n + 1)
        have h₇ : Nat.factorial (n + 1) - 1 + Nat.factorial (n + 1) = 
                  Nat.factorial (n + 1) + Nat.factorial (n + 1) - 1 := by
          omega
        omega
      omega
    rw [h₂]
