import Mathlib

/-- `∑_{i=1}^{n} i * i! = (n + 1)! - 1` for every natural number `n`. -/
theorem m04_sumfact (n : ℕ) :
    ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) =
      Nat.factorial (n + 1) - 1 := by
  have h_fact_pos : ∀ k : ℕ, Nat.factorial k ≥ 1 := by
    intro k
    have : Nat.factorial k ≥ 1 := by
      induction k with
      | zero => simp
      | succ k ih =>
        simp [Nat.factorial]
        nlinarith
    exact this
  
  have h_main : ∀ n : ℕ, ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) =
    Nat.factorial (n + 1) - 1 := by
    intro n
    induction' n with n ih
    · -- Base case: n = 0
      simp [Finset.sum_range_zero, Nat.factorial]
    · -- Inductive step
      rw [Finset.sum_range_succ]
      rw [ih]
      have h₁ : Nat.factorial (n + 1) ≥ 1 := h_fact_pos (n + 1)
      have h₂ : Nat.factorial (n + 1) - 1 + (n + 1) * Nat.factorial (n + 1) = 
        (n + 2) * Nat.factorial (n + 1) - 1 := by
        have : Nat.factorial (n + 1) ≥ 1 := h_fact_pos (n + 1)
        have : Nat.factorial (n + 1) - 1 + (n + 1) * Nat.factorial (n + 1) = 
          (n + 2) * Nat.factorial (n + 1) - 1 := by
          calc
            _ = Nat.factorial (n + 1) - 1 + (n + 1) * Nat.factorial (n + 1) := rfl
            _ = (n + 1) * Nat.factorial (n + 1) + (Nat.factorial (n + 1) - 1) := by ring
            _ = (n + 2) * Nat.factorial (n + 1) - 1 := by
              have : Nat.factorial (n + 1) ≥ 1 := h_fact_pos (n + 1)
              have : (n + 1) * Nat.factorial (n + 1) + Nat.factorial (n + 1) = 
                (n + 2) * Nat.factorial (n + 1) := by
                ring
              have : Nat.factorial (n + 1) - 1 ≤ Nat.factorial (n + 1) := by
                omega
              have : (n + 1) * Nat.factorial (n + 1) + (Nat.factorial (n + 1) - 1) = 
                ((n + 1) * Nat.factorial (n + 1) + Nat.factorial (n + 1)) - 1 := by
                have : Nat.factorial (n + 1) ≥ 1 := h_fact_pos (n + 1)
                omega
              rw [this]
              rw [show (n + 1) * Nat.factorial (n + 1) + Nat.factorial (n + 1) = 
                  (n + 2) * Nat.factorial (n + 1) by ring]
        exact this
      rw [h₂]
      have : (n + 2) * Nat.factorial (n + 1) = Nat.factorial (n + 2) := by
        simp [Nat.factorial, Nat.succ_eq_add_one, mul_comm]
        ring
      rw [this]
  exact h_main n
