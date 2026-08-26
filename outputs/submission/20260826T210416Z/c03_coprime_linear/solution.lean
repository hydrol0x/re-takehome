import Mathlib

/-- Helper: A specific linear combination shows gcd(2n+1, 9n+4) divides 1 -/
lemma helper_divides_one (n : ℕ) (d : ℕ) 
  (h1 : d ∣ 2 * n + 1) (h2 : d ∣ 9 * n + 4) : 
  d ∣ 1 := by
  have h3 : d ∣ 9 * (2 * n + 1) := dvd_mul_of_dvd_right h1 9
  have h4 : d ∣ 2 * (9 * n + 4) := dvd_mul_of_dvd_right h2 2
  have h5 : 9 * (2 * n + 1) = 18 * n + 9 := by ring
  have h6 : 2 * (9 * n + 4) = 18 * n + 8 := by ring
  have h7 : d ∣ 18 * n + 9 := by rw [h5] at h3; exact h3
  have h8 : d ∣ 18 * n + 8 := by rw [h6] at h4; exact h4
  have h9 : d ∣ (18 * n + 9) - (18 * n + 8) := by exact?
  have h10 : (18 * n + 9) - (18 * n + 8) = 1 := by omega
  rw [h10] at h9
  exact h9

/-- Main theorem: For every natural number `n`, the numbers `2 * n + 1` and `9 * n + 4` are coprime. -/
theorem c03_coprime_linear (n : ℕ) : Nat.gcd (2 * n + 1) (9 * n + 4) = 1 := by
  have h1 : Nat.gcd (2 * n + 1) (9 * n + 4) ∣ 2 * n + 1 := Nat.gcd_dvd_left (2 * n + 1) (9 * n + 4)
  have h2 : Nat.gcd (2 * n + 1) (9 * n + 4) ∣ 9 * n + 4 := Nat.gcd_dvd_right (2 * n + 1) (9 * n + 4)
  have h3 : Nat.gcd (2 * n + 1) (9 * n + 4) ∣ 1 := helper_divides_one n (Nat.gcd (2 * n + 1) (9 * n + 4)) h1 h2
  have h4 : Nat.gcd (2 * n + 1) (9 * n + 4) ≤ 1 := Nat.le_of_dvd (by decide) h3
  have h5 : Nat.gcd (2 * n + 1) (9 * n + 4) ≥ 1 := Nat.succ_le_iff.mpr (Nat.gcd_pos_of_pos_left _ (by omega))
  omega
