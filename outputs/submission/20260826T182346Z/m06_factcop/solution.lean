import Mathlib

/-- Any common divisor of `n! + 1` and `(n+1)! + 1` also divides `n`. -/
lemma dvd_common_implies_dvd_n {n d : ℕ} (h1 : d ∣ Nat.factorial n + 1) 
    (h2 : d ∣ Nat.factorial (n + 1) + 1) : d ∣ n := by sorry

/-- If `d` divides both `n` and `n! + 1`, then `d` divides `1`. -/
lemma dvd_n_and_dvd_nfactorial_plus_1_implies_dvd_1 {n d : ℕ} 
    (hn : d ∣ n) (h1 : d ∣ Nat.factorial n + 1) : d ∣ 1 := by sorry

/-- Main theorem: For every `n ≥ 1`, the numbers `n! + 1` and `(n + 1)! + 1` are coprime. -/
theorem m06_factcop (n : ℕ) (hn : 1 ≤ n) :
    Nat.Coprime (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) := by sorry
