import Mathlib

/-- `∑_{i=1}^{n} i * i! = (n + 1)! - 1` for every natural number `n`. -/
theorem m04_sumfact (n : ℕ) :
    ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) =
      Nat.factorial (n + 1) - 1 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      -- expand the sum at `n+1`
      simp [Finset.sum_range_succ, ih, Nat.succ_mul, Nat.factorial_succ,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
        Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
