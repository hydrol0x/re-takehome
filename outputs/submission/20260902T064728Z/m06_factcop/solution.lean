import Mathlib

/-- For every `n ≥ 1`, the numbers `n! + 1` and `(n + 1)! + 1` are coprime. -/
theorem m06_factcop (n : ℕ) (hn : 1 ≤ n) :
    Nat.Coprime (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) := by sorry

-- ==================== HELPER LEMMAS ====================

/-- The expression `(n + 1) * (n! + 1) - ((n + 1)! + 1)` simplifies to `n`. -/
lemma factcop_expr_eq_n (n : ℕ) :
    (n + 1) * (Nat.factorial n + 1) - (Nat.factorial (n + 1) + 1) = n := by sorry

/-- If a natural number `d` divides both `a` and `b`, and `d` divides `a - b`,
    then `d` divides the difference of those values. -/
lemma dvd_sub_of_dvd_both {a b d : ℕ} (hda : d ∣ a) (hdb : d ∣ b) :
    d ∣ a - b := by exact?

/-- If `d` divides `n` and `1 ≤ n`, then `d` divides `n!`. -/
lemma dvd_factorial_of_dvd_n {n d : ℕ} (hn : 1 ≤ n) (hd : d ∣ n) :
    d ∣ Nat.factorial n := by sorry

/-- If `d` divides both `k + 1` and `k`, then `d = 1`. -/
lemma dvd_consecutive_implies_one {d k : ℕ} (h1 : d ∣ k + 1) (h2 : d ∣ k) :
    d = 1 := by sorry

/-- If `d` divides both `Nat.factorial n + 1` and `Nat.factorial (n + 1) + 1`,
    then `d` divides `n`. -/
lemma gcd_common_divisor_divides_n {n d : ℕ} (hn : 1 ≤ n)
    (hd1 : d ∣ Nat.factorial n + 1) (hd2 : d ∣ Nat.factorial (n + 1) + 1) :
    d ∣ n := by sorry

/-- If `d` divides both `Nat.factorial n + 1` and `Nat.factorial n`, then `d = 1`. -/
lemma gcd_divides_one {n d : ℕ} (hd1 : d ∣ Nat.factorial n + 1) (hd2 : d ∣ Nat.factorial n) :
    d = 1 := by exact?

/-- Any common divisor of `Nat.factorial n + 1` and `Nat.factorial (n + 1) + 1` is 1. -/
lemma common_divisor_is_one {n d : ℕ} (hn : 1 ≤ n)
    (hd1 : d ∣ Nat.factorial n + 1) (hd2 : d ∣ Nat.factorial (n + 1) + 1) :
    d = 1 := by sorry
