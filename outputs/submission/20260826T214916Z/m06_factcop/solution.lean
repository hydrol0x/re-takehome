import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Omega
import Mathlib.Tactic.Ring

/-- Helper lemma: (n+1) * (n! + 1) = (n+1)! + (n+1) -/
lemma factorial_linear_combination (n : ℕ) :
    (n + 1) * (Nat.factorial n + 1) = Nat.factorial (n + 1) + (n + 1) := by aesop

/-- Helper lemma: If d divides a and d divides b, then d divides a - b when a ≥ b -/
lemma dvd_sub_of_le {a b d : ℕ} (h₁ : d ∣ a) (h₂ : d ∣ b) (h₃ : b ≤ a) :
    d ∣ a - b := by sorry

/-- Helper lemma: If gcd(a,b) divides c, and gcd(a,b) divides a, then gcd(a,b) divides a-c -/
lemma gcd_dvd_sub {a b c : ℕ} (hgcd : Nat.gcd a b ∣ c) (ha : Nat.gcd a b ∣ a) :
    Nat.gcd a b ∣ a - c := by sorry

/-- Helper lemma: For n ≥ 1, we have n ≤ n! -/
lemma n_le_factorial (n : ℕ) (hn : 1 ≤ n) : n ≤ Nat.factorial n := by sorry

/-- Helper lemma: If d divides 1, then d = 1 -/
lemma dvd_one_eq_one {d : ℕ} (hd : d ∣ 1) : d = 1 := by sorry

/-- Main theorem: For every n ≥ 1, n! + 1 and (n+1)! + 1 are coprime -/
theorem m06_factcop (n : ℕ) (hn : 1 ≤ n) :
    Nat.Coprime (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) := by sorry
