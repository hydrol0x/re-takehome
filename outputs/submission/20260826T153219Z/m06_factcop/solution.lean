import Mathlib

/-- For every `n ≥ 1`, the numbers `n! + 1` and `(n + 1)! + 1` are coprime. -/
theorem m06_factcop (n : ℕ) (hn : 1 ≤ n) :
    Nat.Coprime (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) := by
  have h_main : ∀ d : ℕ, d ∣ (Nat.factorial n + 1) → d ∣ (Nat.factorial (n + 1) + 1) → d ∣ 1 := by
    sorry
  
  have h_gcd_eq_one : (Nat.factorial n + 1).gcd (Nat.factorial (n + 1) + 1) = 1 := by
    exact?
  
  exact h_gcd_eq_one
