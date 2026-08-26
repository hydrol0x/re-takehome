import Mathlib

/-- Helper: Empty sum over range 0 is 0 -/
lemma sum_range_zero : ∑ i ∈ Finset.range 0, (i + 1) * Nat.factorial (i + 1) = 0 := by
  simp [Finset.sum_range_zero]

/-- Helper: Factorial 1 equals 1 -/
lemma factorial_one : Nat.factorial 1 = 1 := by
  norm_num [Nat.factorial]

/-- Helper: For any n, (n + 1)! ≥ 1 -/
lemma factorial_ge_one (n : ℕ) : Nat.factorial (n + 1) ≥ 1 := by
  apply Nat.one_le_of_lt
  exact Nat.factorial_pos (n + 1)

/-- Helper: Key algebraic identity for inductive step -/
lemma factorial_identity (n : ℕ) : 
    Nat.factorial (n + 1) + (n + 1) * Nat.factorial (n + 1) = (n + 2) * Nat.factorial (n + 1) := by
  have h : 1 + (n + 1) = n + 2 := by omega
  calc
    Nat.factorial (n + 1) + (n + 1) * Nat.factorial (n + 1)
      = (1 + (n + 1)) * Nat.factorial (n + 1) := by ring
    _ = (n + 2) * Nat.factorial (n + 1) := by rw [h]

/-- Main theorem: Sum of i * i! from i=1 to n equals (n+1)! - 1 -/
theorem m04_sumfact (n : ℕ) :
    ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) =
      Nat.factorial (n + 1) - 1 := by
  induction' n using Nat.strong_induction_on with n ih
  match n with
  | 0 =>
    -- Base case: empty sum equals 0, and 1! - 1 = 0
    simp [sum_range_zero, factorial_one]
  | n + 1 =>
    -- Inductive step: split the sum into range n plus last term
    have h_sum : ∑ i ∈ Finset.range (n + 1), (i + 1) * Nat.factorial (i + 1)
        = ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) + (n + 1) * Nat.factorial (n + 1) := by
      rw [Finset.sum_range_succ]
    rw [h_sum]
    
    -- Apply induction hypothesis
    have h_ih : ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1)
        = Nat.factorial (n + 1) - 1 := by
      apply ih n (by omega)
    rw [h_ih]
    
    -- Use the factorial identity to combine terms
    have h_fact : Nat.factorial (n + 1) + (n + 1) * Nat.factorial (n + 1)
        = (n + 2) * Nat.factorial (n + 1) := by
      apply factorial_identity
    
    -- Handle the subtraction carefully
    have h_sub : Nat.factorial (n + 1) - 1 + (n + 1) * Nat.factorial (n + 1)
        = (n + 2) * Nat.factorial (n + 1) - 1 := by
      have h_ge : Nat.factorial (n + 1) ≥ 1 := factorial_ge_one n
      have h_eq : (Nat.factorial (n + 1) - 1) + (n + 1) * Nat.factorial (n + 1)
          = Nat.factorial (n + 1) + (n + 1) * Nat.factorial (n + 1) - 1 := by
        have h_add_comm : 1 + (n + 1) * Nat.factorial (n + 1)
            = (n + 1) * Nat.factorial (n + 1) + 1 := by ring
        omega
      calc
        (Nat.factorial (n + 1) - 1) + (n + 1) * Nat.factorial (n + 1)
          = (n + 1) * Nat.factorial (n + 1) + (Nat.factorial (n + 1) - 1) := by ring
        _ = (n + 1) * Nat.factorial (n + 1) + Nat.factorial (n + 1) - 1 := by
          have h_comm : Nat.factorial (n + 1) - 1 + (n + 1) * Nat.factorial (n + 1)
              = (n + 1) * Nat.factorial (n + 1) + (Nat.factorial (n + 1) - 1) := by ring
          omega
        _ = (n + 2) * Nat.factorial (n + 1) - 1 := by
          have h_assoc : Nat.factorial (n + 1) + (n + 1) * Nat.factorial (n + 1)
              = (n + 2) * Nat.factorial (n + 1) := factorial_identity n
          omega
    
    rw [h_sub]
    <;> simp [Nat.factorial]
    <;> ring
    <;> omega
