import Mathlib

/-- `∑_{i=1}^{n} i * i! = (n + 1)! - 1` for every natural number `n`. -/
theorem m04_sumfact (n : ℕ) :
    ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) =
      Nat.factorial (n + 1) - 1 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ (fun i => (i + 1) * Nat.factorial (i + 1)), ih,
          Nat.factorial_succ, Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul,
          Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
          Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
