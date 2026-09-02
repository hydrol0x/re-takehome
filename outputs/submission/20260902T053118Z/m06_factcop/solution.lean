import Mathlib

/-- Helper: For any d dividing both m and m', if d divides m' - m*n, then d divides m*(n+1) - m' - m*n - m = m - m'*n/(m). -/
lemma gcd_helper_1 {a b c : ℕ} (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ (b - c) := by exact?

/-- Helper: If d divides n!+1 and (n+1)!+1, then d divides n. -/
lemma gcd_helper_2 {n : ℕ} (hn : 1 ≤ n) : 
    ∀ d : ℕ, d ∣ (Nat.factorial n + 1) → d ∣ (Nat.factorial (n + 1) + 1) → d ∣ n := by sorry

/-- Helper: If d divides n and d divides n!+1, then d divides 1. -/
lemma gcd_helper_3 {n : ℕ} (hn : 1 ≤ n) : 
    ∀ d : ℕ, d ∣ n → d ∣ (Nat.factorial n + 1) → d ∣ 1 := by sorry

/-- Main helper: If d divides 1, then d = 1. -/
lemma gcd_helper_4 {d : ℕ} : d ∣ 1 → d = 1 := by norm_num

/-- Main theorem: For every `n ≥ 1`, the numbers `n! + 1` and `(n + 1)! + 1` are coprime. -/
theorem m06_factcop (n : ℕ) (hn : 1 ≤ n) :
    Nat.Coprime (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) := by sorry