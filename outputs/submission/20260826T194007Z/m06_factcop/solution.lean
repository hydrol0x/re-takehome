import Mathlib

/-- For every `n ≥ 1`, the numbers `n! + 1` and `(n + 1)! + 1` are coprime. -/
theorem m06_factcop (n : ℕ) (hn : 1 ≤ n) :
    Nat.Coprime (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) := by
  have h_main : Nat.gcd (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) = 1 := by
    sorry
  rw [Nat.coprime_iff_gcd_eq_one]
  exact h_main
