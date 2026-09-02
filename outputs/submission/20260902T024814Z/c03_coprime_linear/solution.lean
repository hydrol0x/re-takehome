import Mathlib

/-- For every natural number `n`, the numbers `2 * n + 1` and `9 * n + 4` are coprime. -/
theorem c03_coprime_linear (n : ℕ) : Nat.gcd (2 * n + 1) (9 * n + 4) = 1 := by sorry

-- Helper: Linear combination shows gcd divides 1
lemma linear_combination_eq_one (n : ℕ) : 
    (2 * n + 1) * 9 - (9 * n + 4) * 2 = 1 := by omega

-- Helper: If gcd divides both a and b, it divides any linear combination
lemma gcd_dvd_linear_combination (d a b x y : ℕ) 
    (h1 : d ∣ a) (h2 : d ∣ b) : d ∣ a * x + b * y := by -- Approach 2: Use existing divisibility lemmas
    have hx : d ∣ a * x := dvd_mul_of_dvd_left h1 x
    have hy : d ∣ b * y := dvd_mul_of_dvd_left h2 y
    exact dvd_add hx hy

-- Helper: From linear combination equal to 1, conclude gcd is 1
lemma gcd_eq_one_of_linear_combination (a b : ℕ) 
    (h : ∃ x y : ℤ, (a : ℤ) * x + (b : ℤ) * y = 1) : Nat.gcd a b = 1 := by sorry
