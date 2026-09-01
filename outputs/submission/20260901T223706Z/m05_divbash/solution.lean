import Mathlib

set_option maxHeartbeats 1000000
set_option exponentiation.threshold 10000
set_option maxRecDepth 8000

/-- For n >= 2, the identity n^2 + 4 = (n - 2)*(n + 2) + 8 holds -/
lemma poly_identity (n : ℕ) (h : 2 ≤ n) :
    n ^ 2 + 4 = (n - 2) * (n + 2) + 8 := by
  rw [show n ^ 2 + 4 = (n - 2) * (n + 2) + 8 by
    cases' le_iff_exists_add.mp h with k hk
    subst hk
    ring_nf
    <;> simp_all [Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib]
    <;> ring_nf at *
    <;> omega]

/-- For n >= 2, (n + 2) ∣ n^2 + 4 iff (n + 2) ∣ 8 -/
lemma dvd_equivalence (n : ℕ) (h : 2 ≤ n) :
    (n + 2) ∣ n ^ 2 + 4 ↔ (n + 2) ∣ 8 := by
  sorry

/-- If n >= 2 and (n + 2) ∣ 8, then n = 2 or n = 6 -/
lemma divisors_of_8 (n : ℕ) (h : 2 ≤ n) (hdiv : (n + 2) ∣ 8) :
    n = 2 ∨ n = 6 := by
  have hbound : n + 2 ≤ 8 := Nat.le_of_dvd (by decide) hdiv
  have hn_le_6 : n ≤ 6 := by omega
  interval_cases n <;> simp_all [Nat.dvd_iff_mod_eq_zero] <;> norm_num <;> tauto

/-- Case n = 1 verification -/
lemma case_n1 (n : ℕ) (hn : 0 < n) (h : n = 1) :
    ¬ (n + 2) ∣ n ^ 2 + 4 := by
  simp_all

/-- Main Theorem proving the iff statement -/
theorem m05_divbash (n : ℕ) (hn : 0 < n) :
    (n + 2) ∣ n ^ 2 + 4 ↔ n = 2 ∨ n = 6 := by
  sorry
