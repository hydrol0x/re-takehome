import Mathlib

/-- `∑_{i=1}^{n} i * i! = (n + 1)! - 1` for every natural number `n`. -/
theorem m04_sumfact (n : ℕ) :
    ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) =
      Nat.factorial (n + 1) - 1 := by
  have h_fact_ge_one : ∀ k : ℕ, 0 < k → 1 ≤ Nat.factorial k := by
    intro k hk
    have : 1 ≤ Nat.factorial k := by
      induction' hk with k hk IH
      · norm_num [Nat.factorial]
      · simp_all [Nat.factorial, Nat.succ_le_iff]
        <;> nlinarith
    exact this
  
  induction' n with n ih
  · -- Base case: n = 0
    simp [Finset.sum_range_zero, Nat.factorial]
  · -- Inductive step: assume true for n, prove for n + 1
    rw [Finset.sum_range_succ, ih]
    have h₁ : 1 ≤ Nat.factorial (n + 1) := h_fact_ge_one (n + 1) (by linarith)
    have h₂ : Nat.factorial (n + 1) - 1 + (n + 1) * Nat.factorial (n + 1) = 
               (n + 2) * Nat.factorial (n + 1) - 1 := by
      have h₃ : Nat.factorial (n + 1) - 1 + (n + 1) * Nat.factorial (n + 1) = 
                 (1 + n + 1) * Nat.factorial (n + 1) - 1 := by
        have h₄ : 1 + n + 1 ≥ 1 := by linarith
        have h₅ : 1 ≤ Nat.factorial (n + 1) := h_fact_ge_one (n + 1) (by linarith)
        calc
          Nat.factorial (n + 1) - 1 + (n + 1) * Nat.factorial (n + 1) =
              (Nat.factorial (n + 1) - 1) + (n + 1) * Nat.factorial (n + 1) := rfl
          _ = (1 + (n + 1)) * Nat.factorial (n + 1) - 1 := by
            have h₆ : Nat.factorial (n + 1) ≥ 1 := by linarith
            have h₇ : Nat.factorial (n + 1) - 1 + (n + 1) * Nat.factorial (n + 1) = 
                       (n + 1 + 1) * Nat.factorial (n + 1) - 1 := by
              rw [← Nat.add_sub_cancel' h₆]
              ring_nf
              <;> omega
            simpa [add_assoc, add_comm, add_left_comm] using h₇
          _ = (1 + n + 1) * Nat.factorial (n + 1) - 1 := by ring
      calc
        Nat.factorial (n + 1) - 1 + (n + 1) * Nat.factorial (n + 1) =
            (1 + n + 1) * Nat.factorial (n + 1) - 1 := h₃
        _ = (n + 2) * Nat.factorial (n + 1) - 1 := by ring
    rw [h₂]
    simp [Nat.factorial, mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc]
    <;> ring_nf
    <;> simp_all [Nat.factorial]
    <;> omega
