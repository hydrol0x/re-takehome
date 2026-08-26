import Mathlib

/-- `∑_{i=1}^{n} i * i! = (n + 1)! - 1` for every natural number `n`. -/
theorem m04_sumfact (n : ℕ) :
    ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) =
      Nat.factorial (n + 1) - 1 := by
  have h_base : Nat.factorial 1 ≥ 1 := by decide
  have h_ind : ∀ k : ℕ, (∑ i ∈ Finset.range k, (i + 1) * Nat.factorial (i + 1)) = Nat.factorial (k + 1) - 1 →
    (∑ i ∈ Finset.range (k + 1), (i + 1) * Nat.factorial (i + 1)) = Nat.factorial (k + 2) - 1 := by
    intro k ih
    rw [Finset.sum_range_succ]
    have h_fact_pos : Nat.factorial (k + 1) > 0 := Nat.factorial_pos (k + 1)
    have h_mul_pos : (k + 2) * Nat.factorial (k + 2) > 0 := by
      apply Nat.mul_pos
      · omega
      · exact Nat.factorial_pos (k + 2)
    simp_all [Nat.factorial_succ, Nat.add_sub_cancel_left]
    <;> ring_nf at *
    <;> omega
  
  induction n using Nat.strong_induction_on with
  | h n ihn =>
    match n with
    | 0 => simp
    | (n + 1) =>
      have h₁ := h_ind n (ihn n (by omega))
      simpa [Finset.sum_range_succ, Nat.succ_eq_add_one] using h₁
