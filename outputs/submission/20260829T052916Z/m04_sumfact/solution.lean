import Mathlib

/-- `∑_{i=1}^{n} i * i! = (n + 1)! - 1` for every natural number `n`. -/
theorem m04_sumfact (n : ℕ) :
    ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) =
      Nat.factorial (n + 1) - 1 := by
  induction' n with n ih
  · -- Base case: n = 0
    simp [Nat.factorial]
  · -- Inductive step: assume true for n, prove for n+1
    rw [Finset.sum_range_succ, ih]
    have h_fact_pos : Nat.factorial (n + 1) ≥ 1 := Nat.succ_le_of_lt (Nat.factorial_pos _)
    have h_sub_add : Nat.factorial (n + 1) - 1 + (n + 1) * Nat.factorial (n + 1) = (n + 2) * Nat.factorial (n + 1) - 1 := by
      have h_mul_comm : (n + 1) * Nat.factorial (n + 1) = Nat.factorial (n + 1) * (n + 1) := by ring
      rw [h_mul_comm]
      have h_add : Nat.factorial (n + 1) + Nat.factorial (n + 1) * (n + 1) = Nat.factorial (n + 1) * (n + 2) := by
        ring
      have h_factorial : (n + 2) * Nat.factorial (n + 1) = Nat.factorial (n + 2) := by
        rw [Nat.factorial_succ (n + 1)]
        <;> ring
      -- Use omega or direct calculation to handle the subtraction
      have h_cases : Nat.factorial (n + 1) ≥ 1 := Nat.succ_le_of_lt (Nat.factorial_pos _)
      -- Work with the actual arithmetic
      cases n with
      | zero =>
        norm_num [Nat.factorial] at *
      | succ k =>
        simp_all [Nat.factorial_succ, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.mul_assoc]
        <;> ring_nf at *
        <;> omega
    simp_all [Nat.factorial_succ, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.mul_assoc]
    <;> ring_nf at *
    <;> omega
