import Mathlib

/-- Helper lemma: base case for the sumfact theorem -/
lemma m04_sumfact_base :
    ∑ i ∈ Finset.range 0, (i + 1) * Nat.factorial (i + 1) = Nat.factorial (0 + 1) - 1 := by
  simp [Nat.factorial]

/-- Helper lemma: inductive step helper for sumfact theorem -/
lemma m04_sumfact_step_helper (n : ℕ) :
    Nat.factorial (n + 1) + (n + 1) * Nat.factorial (n + 1) = Nat.factorial (n + 2) := by
  rw [show Nat.factorial (n + 2) = (n + 2) * Nat.factorial (n + 1) by
    rw [Nat.factorial_succ, mul_comm]]
  ring

/-- Main theorem: telescoping factorial identity -/
theorem m04_sumfact (n : ℕ) :
    ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) =
      Nat.factorial (n + 1) - 1 := by
  induction n with
  | zero => simp [m04_sumfact_base]
  | succ n ih =>
    have h₁ : ∑ i ∈ Finset.range (n + 1), (i + 1) * Nat.factorial (i + 1) =
        ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) + (n + 1) * Nat.factorial (n + 1) := by
      simp [Finset.sum_range_succ]
    
    rw [h₁]
    rw [ih]
    
    have h₂ : Nat.factorial (n + 1) ≥ 1 := by
      apply Nat.succ_le_of_lt
      apply Nat.factorial_pos
    
    have h₃ : Nat.factorial (n + 1) - 1 + (n + 1) * Nat.factorial (n + 1) =
        (Nat.factorial (n + 1) + (n + 1) * Nat.factorial (n + 1)) - 1 := by
      omega
    
    rw [h₃]
    rw [m04_sumfact_step_helper]
    <;> simp [Nat.factorial_succ, add_assoc]
    <;> omega
