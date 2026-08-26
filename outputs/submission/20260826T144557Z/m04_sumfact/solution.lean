import Mathlib

/-- `∑_{i=1}^{n} i * i! = (n + 1)! - 1` for every natural number `n`. -/
theorem m04_sumfact (n : ℕ) :
    ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) =
      Nat.factorial (n + 1) - 1 := by
  have h : ∀ n : ℕ, ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) = Nat.factorial (n + 1) - 1 := by
    intro n
    induction' n with n ih
    · simp
    rw [Finset.sum_range_succ]
    have h1 : 0 < Nat.factorial (n + 1) := Nat.factorial_pos (n + 1)
    simp [ih, Nat.succ_eq_add_one] at *
    cases n with
    | zero => simp
    | succ n =>
      norm_num [Nat.factorial] at *
      ring_nf at *
      omega
  
  apply h
