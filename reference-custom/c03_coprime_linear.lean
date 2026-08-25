import Mathlib

/-- For every natural number `n`, the numbers `2 * n + 1` and `9 * n + 4` are coprime. -/
theorem c03_coprime_linear (n : ℕ) : Nat.gcd (2 * n + 1) (9 * n + 4) = 1 := by
  have h1 : Nat.gcd (2 * n + 1) (9 * n + 4) ∣ 2 * n + 1 := Nat.gcd_dvd_left _ _
  have h2 : Nat.gcd (2 * n + 1) (9 * n + 4) ∣ 9 * n + 4 := Nat.gcd_dvd_right _ _
  have h3 : Nat.gcd (2 * n + 1) (9 * n + 4) ∣ 9 * (2 * n + 1) - 2 * (9 * n + 4) :=
    Nat.dvd_sub (h1.mul_left 9) (h2.mul_left 2)
  have h4 : 9 * (2 * n + 1) - 2 * (9 * n + 4) = 1 := by omega
  rw [h4] at h3
  exact Nat.dvd_one.mp h3
