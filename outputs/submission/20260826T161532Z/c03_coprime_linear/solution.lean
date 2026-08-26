import Mathlib

/-- For every natural number `n`, the numbers `2 * n + 1` and `9 * n + 4` are coprime. -/
theorem c03_coprime_linear (n : ℕ) : Nat.gcd (2 * n + 1) (9 * n + 4) = 1 := by sorry

-- Helper lemmas below

lemma gcd_reduction_1 (n : ℕ) : 
  Nat.gcd (2 * n + 1) (9 * n + 4) = Nat.gcd (2 * n + 1) n := by calc
    Nat.gcd (2 * n + 1) (9 * n + 4)
      = Nat.gcd (2 * n + 1) (n + 4 * (2 * n + 1)) := by
        have h : 9 * n + 4 = n + 4 * (2 * n + 1) := by ring
        rw [h]
    _ = Nat.gcd (2 * n + 1) n := by
      exact Nat.gcd_add_mul_right_right _ _ 4

lemma gcd_reduction_2 (n : ℕ) : 
  Nat.gcd (2 * n + 1) n = 1 := by norm_num

lemma main_proof (n : ℕ) : Nat.gcd (2 * n + 1) (9 * n + 4) = 1 := by exact?
