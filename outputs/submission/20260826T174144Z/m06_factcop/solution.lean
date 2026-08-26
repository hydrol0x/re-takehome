import Mathlib

/-- For every `n ≥ 1`, the numbers `n! + 1` and `(n + 1)! + 1` are coprime. -/
theorem m06_factcop (n : ℕ) (hn : 1 ≤ n) :
    Nat.Coprime (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) := by
  have h_factorial_mul : ∀ k : ℕ, (k + 1) * Nat.factorial k = Nat.factorial (k + 1) := by aesop
  have h_diff_divides_n : ∀ d : ℕ, d ∣ (Nat.factorial n + 1) → d ∣ (Nat.factorial (n + 1) + 1) → d ∣ n := by sorry
  have h_coprime_implies_one : ∀ d : ℕ, d ∣ (Nat.factorial n + 1) → d ∣ n → d ∣ 1 := by sorry
  have h_main : Nat.Coprime (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) := by sorry
  exact h_main
