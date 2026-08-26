import Mathlib

/-- `∑_{i=1}^{n} i * i! = (n + 1)! - 1` for every natural number `n`. -/
theorem m04_sumfact (n : ℕ) :
    ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) =
      Nat.factorial (n + 1) - 1 := by
  induction' n with n ih
  · -- Base case: n = 0
    simp [Finset.sum_range_zero, Nat.factorial]
  · -- Inductive step: assume for n, prove for n + 1
    rw [Finset.sum_range_succ]
    rw [ih]
    have h₁ : Nat.factorial (n + 1) ≥ 1 := Nat.factorial_pos (n + 1)
    have h₂ : Nat.factorial (n + 1) + (n + 1) * Nat.factorial (n + 1) = (n + 2) * Nat.factorial (n + 1) := by
      ring
    have h₃ : (n + 2) * Nat.factorial (n + 1) = Nat.factorial (n + 2) := by
      simp [Nat.factorial, mul_comm]
      <;> ring
    simp_all [Nat.factorial, Nat.mul_sub_left_distrib, Nat.add_assoc]
    <;> ring_nf at *
    <;> omega
