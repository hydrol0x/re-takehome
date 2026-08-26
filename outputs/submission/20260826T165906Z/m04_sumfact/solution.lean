import Mathlib

/-- Base case: empty sum equals 0, and (0+1)! - 1 = 0 -/
lemma factorial_sum_base :
    ∑ i ∈ Finset.range 0, (i + 1) * Nat.factorial (i + 1) =
      Nat.factorial (0 + 1) - 1 := by norm_num

/-- Key algebraic identity: (k+1)! - 1 + (k+1)*(k+1)! = (k+2)! - 1 -/
lemma factorial_inductive_identity (k : ℕ) :
    (Nat.factorial (k + 1) - 1) + (k + 1) * Nat.factorial (k + 1) =
      Nat.factorial (k + 2) - 1 := by sorry

/-- Split finite range sum at the last element -/
lemma finset_range_succ_split (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (i + 1) * Nat.factorial (i + 1) =
      ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) + (n + 1) * Nat.factorial (n + 1) := by exact?

/-- Main theorem: telescoping factorial identity -/
theorem m04_sumfact (n : ℕ) :
    ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) =
      Nat.factorial (n + 1) - 1 := by
  induction n with
  | zero =>
    -- Base case: both sides equal 0
    rw [factorial_sum_base]
  | succ n ih =>
    -- Inductive step: use previous result and algebraic identity
    rw [finset_range_succ_split]
    rw [ih]
    rw [factorial_inductive_identity]
