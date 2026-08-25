import Mathlib

/-- For every `n ≥ 1`, the numbers `n! + 1` and `(n + 1)! + 1` are coprime. -/
theorem m06_factcop (n : ℕ) (hn : 1 ≤ n) :
    Nat.Coprime (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) := by
  have h_algebra : (n + 1) * (Nat.factorial n + 1) = (Nat.factorial (n + 1) + 1) + n := by exact?
  have h_main : ∀ d : ℕ, d ∣ (Nat.factorial n + 1) → d ∣ (Nat.factorial (n + 1) + 1) → d ∣ 1 := by sorry
  have h_coprime : Nat.Coprime (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) := by exact?
  exact h_coprime

-- Helper lemmas above the main theorem
