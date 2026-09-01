import Mathlib

theorem m04_sumfact (n : ℕ) :
    ∑ i ∈ Finset.range n, (i + 1) * Nat.factorial (i + 1) =
      Nat.factorial (n + 1) - 1 := by
  induction n with
  | zero =>
    simp [Finset.sum_range_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    -- We have: ((n + 1).factorial - 1) + (n + 1 + 1) * (n + 1 + 1).factorial
    -- Goal: (n + 1 + 1).factorial - 1
    -- Let k = n + 1. We have (k! - 1) + (k + 1) * (k + 1)! = (k + 2)! - 1
    -- Simplify arithmetic
    
    -- First, note that (n + 1).factorial >= 1, so we can manipulate subtractions safely
    have h_fact_pos : 1 ≤ (n + 1).factorial := by
      apply Nat.succ_le_of_lt
      exact Nat.factorial_pos _
    
    -- Rewrite the expression to group factorials
    -- (n + 1)! - 1 + (n + 2) * (n + 2)!
    -- Wait, the term added is (n + 1 + 1) * (n + 1 + 1)! = (n + 2) * (n + 2)!
    -- Wait, looking at the loop index.
    -- range (n + 1) sums up to n. The last term is for i = n.
    -- Term is (n + 1) * (n + 1)!
    -- My manual derivation above was slightly off in indices vs Lean code.
    -- Let's re-verify.
    -- Sum range n: i goes 0..n-1. Last term i=n-1 -> (n)*n!.
    -- Sum range (n+1): i goes 0..n. Last term i=n -> (n+1)*(n+1)!.
    -- IH: Sum range n = (n+1)! - 1.
    -- Step: Sum range (n+1) = Sum range n + term(n)
    -- = ((n+1)! - 1) + (n+1)*(n+1)!
    -- We want to reach (n+2)! - 1.
    -- So we need (n+1)! - 1 + (n+1)*(n+1)! = (n+2)! - 1.
    -- Add 1 to both sides: (n+1)! + (n+1)*(n+1)! = (n+2)!
    -- Factor: (n+1)! * (1 + n + 1) = (n+2)!
    -- (n+1)! * (n+2) = (n+2)!
    -- This is true.
    
    -- In Lean:
    -- rw [Nat.factorial_succ, mul_comm]
    -- ring_nf
    -- simp [Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib] -- maybe not needed
    
    -- Let's try to make the simplification explicit.
    -- We have A - 1 + B. We want C - 1.
    -- If A + B = C, then A - 1 + B = C - 1 requires A >= 1.
    -- Here A = (n+1)!, B = (n+1)*(n+1)!.
    -- A + B = (n+1)! * (1 + n + 1) = (n+1)! * (n+2) = (n+2)! = C.
    -- So we need to show (n+1)! >= 1.
    
    simp_all [Nat.factorial_succ, Nat.mul_add, Nat.add_mul, Nat.add_assoc]
    <;> ring_nf at *
    <;> omega
