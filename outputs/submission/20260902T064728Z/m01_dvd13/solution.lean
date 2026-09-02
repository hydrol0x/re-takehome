import Mathlib

-- Helper Lemma: Power expansion for base 4 in the induction step
lemma pow_4_step (n : ℕ) : 4 ^ (2 * (n + 1) + 1) = 4 ^ (2 * n + 1) * 16 := by ring

-- Helper Lemma: Power expansion for base 3 in the induction step
lemma pow_3_step (n : ℕ) : 3 ^ (n + 1 + 2) = 3 ^ (n + 2) * 3 := by ring

-- Helper Lemma: Algebraic decomposition of the expression at n+1
-- Shows that the term at n+1 equals 13 times a term plus 3 times the term at n
lemma expr_decomposition (n : ℕ) :
    4 ^ (2 * (n + 1) + 1) + 3 ^ (n + 1 + 2) =
    13 * 4 ^ (2 * n + 1) + 3 * (4 ^ (2 * n + 1) + 3 ^ (n + 2)) := by ring

/-- For every natural number `n`, `13` divides `4 ^ (2 * n + 1) + 3 ^ (n + 2)`. -/
theorem m01_dvd13 (n : ℕ) : 13 ∣ 4 ^ (2 * n + 1) + 3 ^ (n + 2) := by induction n with
| zero => simp [Nat.dvd_iff_mod_eq_zero]
| succ n ih =>
rw [expr_decomposition]
exact dvd_add (by simp [Nat.dvd_mul_right]) (by exact ih.mul_left 3)
