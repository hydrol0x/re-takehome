import Mathlib

/-- Algebraic identity: (n+1)(n! + 1) = (n+1)! + n + 1 -/
lemma factorial_identity (n : ℕ) :
    (n + 1) * (Nat.factorial n + 1) = Nat.factorial (n + 1) + n + 1 := by aesop

/-- If d divides both a and b, then d divides their gcd -/
lemma dvd_gcd_of_dvd_both {a b d : ℕ} (h1 : d ∣ a) (h2 : d ∣ b) :
    d ∣ Nat.gcd a b := by exact?

/-- If d divides a and d divides b+1, then d divides gcd(a,b+1) -/
lemma dvd_gcd_add_one {a b d : ℕ} (h1 : d ∣ a) (h2 : d ∣ b + 1) :
    d ∣ Nat.gcd a (b + 1) := by exact?

/-- If gcd(a,b) = 1 and d divides both a and b, then d = 1 -/
lemma gcd_eq_one_implies_unit_divisor {a b d : ℕ} 
    (h_gcd : Nat.gcd a b = 1) (h1 : d ∣ a) (h2 : d ∣ b) :
    d = 1 := by exact?

/-- For n ≥ 1, factorial n > 0 -/
lemma factorial_pos (n : ℕ) (hn : 1 ≤ n) : 0 < Nat.factorial n := by positivity

/-- Main theorem: m06_factcop -/
theorem m06_factcop (n : ℕ) (hn : 1 ≤ n) :
    Nat.Coprime (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) := by sorry
