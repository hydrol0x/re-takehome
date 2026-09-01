import Mathlib

/-- `∑_{i=1}^{n} i * i! = (n + 1)! - 1` for every natural number `n`. -/
theorem m04_sumfact (n : ℕ) :
    ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) =
      Nat.factorial (n + 1) - 1 := by
  -- rewrite each summand as a difference of consecutive factorials
  have h_term :
      ∀ i : ℕ, (i + 1) * Nat.factorial (i + 1) =
        Nat.factorial (i + 2) - Nat.factorial (i + 1) := by
    intro i
    have h₁ :
        ((i + 2) * Nat.factorial (i + 1)) - Nat.factorial (i + 1) =
          (i + 1) * Nat.factorial (i + 1) := by
      have h := Nat.succ_mul (i + 1) (Nat.factorial (i + 1))
      -- (i+2) * k = (i+1) * k + k
      simpa [h] using Nat.add_sub_cancel ((i + 1) * Nat.factorial (i + 1))
        (Nat.factorial (i + 1))
    calc
      (i + 1) * Nat.factorial (i + 1)
          = ((i + 2) * Nat.factorial (i + 1)) - Nat.factorial (i + 1) := by
            simpa [h₁]
      _ = Nat.factorial (i + 2) - Nat.factorial (i + 1) := by
            simpa using Nat.factorial_succ (i + 1)
  -- replace the sum with the telescoping sum
  have h_sum :
      ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) =
        ∑ i ∈ Finset.range n, (Nat.factorial (i + 2) - Nat.factorial (i + 1)) := by
    apply Finset.sum_congr rfl
    intro i hi
    simpa [h_term i]
  -- evaluate the telescoping sum
  have h_tel :
      ∑ i ∈ Finset.range n, (Nat.factorial (i + 2) - Nat.factorial (i + 1)) =
        Nat.factorial (n + 1) - Nat.factorial 1 := by
    induction n with
    | zero =>
        simp
    | succ n ih =>
        have hle : Nat.factorial (n + 1) ≤ Nat.factorial (n + 2) := by
          have : n + 1 ≤ n + 2 := Nat.le_succ _
          exact Nat.factorial_le this
        simp [Finset.sum_range_succ, ih, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
              Nat.sub_add_cancel hle]
  simpa [Nat.factorial_one, h_sum] using h_tel
