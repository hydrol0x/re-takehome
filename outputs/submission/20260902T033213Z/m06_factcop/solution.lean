import Mathlib

/-- For n ≥ 1, we have (n+1)! + 1 = (n+1) * (n! + 1) - n. -/
lemma factcop_relation (n : ℕ) (hn : 1 ≤ n) :
    Nat.factorial (n + 1) + 1 = (n + 1) * (Nat.factorial n + 1) - n := by sorry

/-- If d divides a and d divides b, and b ≤ c*a, then d divides c*a - b. -/
lemma dvd_sub_of_le_mul {a b c d : ℕ} (ha : d ∣ a) (hb : d ∣ b) (hle : b ≤ c * a) :
    d ∣ c * a - b := by sorry

/-- If d divides n and n ≥ 1, then d divides n!. -/
lemma dvd_n_implies_dvd_factorial (n d : ℕ) (hd : d ∣ n) (hn : 1 ≤ n) :
    d ∣ Nat.factorial n := by sorry

/-- If d divides both a and a+1, then d = 1. -/
lemma dvd_consecutive_numbers {a d : ℕ} (ha : d ∣ a) (ha1 : d ∣ a + 1) :
    d = 1 := by sorry

/-- Main theorem: For every n ≥ 1, the numbers n! + 1 and (n+1)! + 1 are coprime. -/
theorem m06_factcop (n : ℕ) (hn : 1 ≤ n) :
    Nat.Coprime (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) := by sorry
