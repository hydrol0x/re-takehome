import Mathlib

/-- `∑_{i=1}^{n} i * i! = (n + 1)! - 1` for every natural number `n`. -/
theorem m04_sumfact (n : ℕ) :
    ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) =
      Nat.factorial (n + 1) - 1 := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hpos : 1 ≤ Nat.factorial (n + 1) :=
        Nat.succ_le_of_lt (Nat.factorial_pos _)
      calc
        ∑ i ∈ Finset.range (n + 1), (i + 1) * Nat.factorial (i + 1)
            = (∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1)) +
                (n + 1) * Nat.factorial (n + 1) := by
              simpa [Finset.sum_range_succ]
        _ = (Nat.factorial (n + 1) - 1) + (n + 1) * Nat.factorial (n + 1) := by
              simpa [ih]
        _ = Nat.factorial (n + 1) + (n + 1) * Nat.factorial (n + 1) - 1 := by
