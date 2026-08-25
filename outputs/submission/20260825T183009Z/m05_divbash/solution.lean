import Mathlib

set_option maxHeartbeats 1000000

lemma dvd_n_sq_plus_4_imp_dvd_4n (n : ℕ) (hn : 0 < n) (h : (n + 2) ∣ n ^ 2 + 4) : (n + 2) ∣ 4 * n := by sorry

lemma dvd_4n_imp_dvd_8 (n : ℕ) (hn : 0 < n) (h : (n + 2) ∣ 4 * n) : (n + 2) ∣ 8 := by sorry

lemma dvd_8_imp_bound (n : ℕ) (hn : 0 < n) (h : (n + 2) ∣ 8) : n ≤ 6 := by sorry

theorem m05_divbash (n : ℕ) (hn : 0 < n) :
    (n + 2) ∣ n ^ 2 + 4 ↔ n = 2 ∨ n = 6 := by
  constructor
  · intro h
    have h4n := dvd_n_sq_plus_4_imp_dvd_4n n hn h
    have h8 := dvd_4n_imp_dvd_8 n hn h4n
    have hbound := dvd_8_imp_bound n hn h8
    interval_cases n <;> simp_all [Nat.dvd_iff_mod_eq_zero] <;> decide
  · intro h
    cases h
    · subst n
      decide
    · subst n
      decide
