import Mathlib

/-- For every `n ≥ 1`, the numbers `n! + 1` and `(n + 1)! + 1` are coprime. -/
theorem m06_factcop (n : ℕ) (hn : 1 ≤ n) :
    Nat.Coprime (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) := by sorry

-- Helper lemma: (n+1)! = (n+1) * n!
lemma fact_succ_eq (n : ℕ) :
    Nat.factorial (n + 1) = (n + 1) * Nat.factorial n := by aesop

-- Helper lemma: If d divides both n!+1 and (n+1)!+1, then d divides n
lemma common_divisor_divides_n (n : ℕ) (hn : 1 ≤ n) (d : ℕ)
    (hd1 : d ∣ Nat.factorial n + 1) (hd2 : d ∣ Nat.factorial (n + 1) + 1) :
    d ∣ n := by sorry

-- Helper lemma: If d divides n and n ≥ 1, then d divides n!
lemma dvd_n_implies_dvd_fact (n : ℕ) (hn : 1 ≤ n) (d : ℕ) (hd : d ∣ n) :
    d ∣ Nat.factorial n := by sorry

-- Helper lemma: If d divides both a+1 and a, then d divides 1
lemma dvd_both_implies_one (a d : ℕ) (h1 : d ∣ a + 1) (h2 : d ∣ a) :
    d ∣ 1 := by exact?

-- Helper lemma: Coprime is equivalent to gcd = 1
lemma coprime_iff_gcd_one (a b : ℕ) :
    Nat.Coprime a b ↔ Nat.gcd a b = 1 := by norm_num

-- Helper lemma: If any common divisor d equals 1, then gcd = 1
lemma all_common_divisors_one_implies_gcd_one (a b : ℕ) :
    (∀ d : ℕ, d ∣ a → d ∣ b → d = 1) → Nat.gcd a b = 1 := by sorry

-- Helper lemma: From coprime, we can conclude gcd = 1
lemma gcd_one_from_coprime (a b : ℕ) (h : Nat.Coprime a b) :
    Nat.gcd a b = 1 := by linarith
