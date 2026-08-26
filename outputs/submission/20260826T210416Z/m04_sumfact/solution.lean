import Mathlib

/-- Helper lemma: factorial of positive numbers is at least 1 -/
lemma factorial_pos (n : ℕ) : 1 ≤ Nat.factorial (n + 1) := by
  have h : 1 ≤ Nat.factorial (n + 1) := by
    apply Nat.succ_le_of_lt
    exact Nat.factorial_pos (n + 1)
  exact h

/-- Helper lemma: (n + 1) * (n + 1)! + (n + 1)! = (n + 2)! -/
lemma factorial_recurrence (n : ℕ) :
    (n + 1) * Nat.factorial (n + 1) + Nat.factorial (n + 1) = Nat.factorial (n + 2) := by
  have h₁ : Nat.factorial (n + 2) = (n + 2) * Nat.factorial (n + 1) := by
    rw [Nat.factorial_succ]
    <;> ring
  rw [h₁]
  ring

/-- Main theorem: telescoping factorial identity -/
theorem m04_sumfact (n : ℕ) :
    ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) =
      Nat.factorial (n + 1) - 1 := by
  have h_base : ∑ i ∈ Finset.range 0, (i + 1) * Nat.factorial (i + 1) = Nat.factorial (0 + 1) - 1 := by
    simp [Finset.sum_range_zero]
    <;> norm_num
  
  have h_ind_step (n : ℕ) (IH : ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) = Nat.factorial (n + 1) - 1) :
      ∑ i ∈ Finset.range (n + 1), (i + 1) * Nat.factorial (i + 1) = Nat.factorial (n + 2) - 1 := by
    have h₁ : ∑ i ∈ Finset.range (n + 1), (i + 1) * Nat.factorial (i + 1) =
        ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) + (n + 1) * Nat.factorial (n + 1) := by
      rw [Finset.sum_range_succ]
      <;> simp [add_assoc]
    
    rw [h₁]
    rw [IH]
    
    have h₂ : 1 ≤ Nat.factorial (n + 1) := factorial_pos n
    have h₃ : Nat.factorial (n + 1) - 1 + (n + 1) * Nat.factorial (n + 1) =
        (n + 1) * Nat.factorial (n + 1) + Nat.factorial (n + 1) - 1 := by
      omega
    
    rw [h₃]
    have h₄ : (n + 1) * Nat.factorial (n + 1) + Nat.factorial (n + 1) = Nat.factorial (n + 2) :=
      factorial_recurrence n
    rw [h₄]
    <;> omega
  
  induction n with
  | zero =>
    exact h_base
  | succ n ih =>
    exact h_ind_step n ih
