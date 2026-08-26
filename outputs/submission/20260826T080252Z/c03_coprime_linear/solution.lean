import Mathlib

/-- For every natural number `n`, the numbers `2 * n + 1` and `9 * n + 4` are coprime. -/
theorem c03_coprime_linear (n : ℕ) : Nat.gcd (2 * n + 1) (9 * n + 4) = 1 := by sorry

lemma coprime_linear_combination (n : ℕ) : 
  9 * (2 * n + 1) - 2 * (9 * n + 4) = 1 := by omega

lemma dvd_linear_combination {a b c d : ℕ} (h1 : d ∣ a) (h2 : d ∣ b) (k1 k2 : ℕ) :
  d ∣ k1 * a - k2 * b := by sorry

lemma dvd_one_implies_one (d : ℕ) : d ∣ 1 → d = 1 := by norm_num

lemma gcd_eq_one_of_dvd_one (n : ℕ) : 
  ∀ d : ℕ, d ∣ Nat.gcd (2 * n + 1) (9 * n + 4) → d ∣ 1 := by sorry

lemma gcd_is_one (n : ℕ) : 
  Nat.gcd (2 * n + 1) (9 * n + 4) = 1 := by exact?
