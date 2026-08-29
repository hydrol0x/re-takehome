import Mathlib

/-- For every `n ≥ 1`, the numbers `n! + 1` and `(n + 1)! + 1` are coprime. -/
theorem m06_factcop (n : ℕ) (hn : 1 ≤ n) :
    Nat.Coprime (Nat.factorial n + 1) (Nat.factorial (n + 1) + 1) := by sorry

-- Helper: (n+1)! = (n+1) * n!
lemma factorial_succ_eq_mul_factorial (n : ℕ) :
    Nat.factorial (n + 1) = (n + 1) * Nat.factorial n := by aesop

-- Helper: For n ≥ 1, d | n implies d | n!
lemma dvd_of_dvd_factorial_of_ge (n : ℕ) (h : 1 ≤ n) {d : ℕ} (hd : d ∣ n) :
    d ∣ Nat.factorial n := by sorry

-- Helper: Compute the difference (n+1)*(n!+1) - ((n+1)!+1) = n
lemma diff_computes_to_n (n : ℕ) :
    (n + 1) * (Nat.factorial n + 1) - (Nat.factorial (n + 1) + 1) = n := by calc
      (n + 1) * (Nat.factorial n + 1) - (Nat.factorial (n + 1) + 1)
          = (n + 1) * (Nat.factorial n + 1) - ((n + 1) * Nat.factorial n + 1) := by rw [factorial_succ_eq_mul_factorial]
      _ = (n + 1) * Nat.factorial n + (n + 1) - ((n + 1) * Nat.factorial n + 1) := by ring_nf
      _ = n := by omega

-- Helper: If d divides both a and b, then d divides gcd(a,b)
lemma dvd_gcd_of_dvd_both (a b d : ℕ) (ha : d ∣ a) (hb : d ∣ b) :
    d ∣ Nat.gcd a b := by exact?

-- Main helper: Any common divisor of (n!+1) and ((n+1)!+1) divides 1
lemma any_common_divisor_divides_one (n : ℕ) (hn : 1 ≤ n) {d : ℕ}
    (h1 : d ∣ Nat.factorial n + 1) (h2 : d ∣ Nat.factorial (n + 1) + 1) :
    d ∣ 1 := by sorry

-- Alternative characterization: gcd a b = 1 iff any common divisor divides 1
lemma gcd_eq_one_iff_any_dvd_one (a b : ℕ) :
    Nat.gcd a b = 1 ↔ ∀ d, d ∣ a → d ∣ b → d ∣ 1 := by sorry
