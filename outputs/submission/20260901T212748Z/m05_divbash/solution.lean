import Mathlib

/-- Helper: If (n+2) divides n^2 + 4, then (n+2) divides 4n. -/
lemma div_n2_plus_4_implies_div_4n {n : ℕ} (h : (n + 2) ∣ n ^ 2 + 4) : (n + 2) ∣ 4 * n := by sorry

/-- Helper: If (n+2) divides 4n, then (n+2) divides 8. -/
lemma div_4n_implies_div_8 {n : ℕ} (h : (n + 2) ∣ 4 * n) : (n + 2) ∣ 8 := by sorry

/-- Helper: Combined: if (n+2) divides n^2 + 4, then (n+2) divides 8. -/
lemma div_n2_plus_4_implies_div_8 {n : ℕ} (h : (n + 2) ∣ n ^ 2 + 4) : (n + 2) ∣ 8 := by exact div_4n_implies_div_8 (div_n2_plus_4_implies_div_4n h)

/-- Helper: For positive n, if (n+2) divides 8, then n ≤ 6. -/
lemma div_8_implies_bound {n : ℕ} (hn : 0 < n) (h : (n + 2) ∣ 8) : n ≤ 6 := by sorry

/-- Helper: n = 2 satisfies (n+2) | n^2 + 4. -/
lemma case_n_eq_2 : (2 + 2) ∣ 2 ^ 2 + 4 := by norm_num

/-- Helper: n = 6 satisfies (n+2) | n^2 + 4. -/
lemma case_n_eq_6 : (6 + 2) ∣ 6 ^ 2 + 4 := by norm_num

/-- Helper: For n ∈ {1,2,3,4,5}, only n=2 works. -/
lemma check_small_cases {n : ℕ} (hn : 0 < n) (hn_le : n ≤ 5) : (n + 2) ∣ n ^ 2 + 4 → n = 2 := by sorry

/-- Forward direction: if (n+2) | n^2 + 4, then n = 2 or n = 6. -/
lemma m05_forward {n : ℕ} (hn : 0 < n) (h : (n + 2) ∣ n ^ 2 + 4) : n = 2 ∨ n = 6 := by sorry

/-- Backward direction: if n = 2 or n = 6, then (n+2) | n^2 + 4. -/
lemma m05_backward {n : ℕ} (hn : 0 < n) (h : n = 2 ∨ n = 6) : (n + 2) ∣ n ^ 2 + 4 := by aesop

/-- Main theorem: (n+2) divides n^2 + 4 iff n = 2 or n = 6. -/
theorem m05_divbash (n : ℕ) (hn : 0 < n) :
    (n + 2) ∣ n ^ 2 + 4 ↔ n = 2 ∨ n = 6 := by sorry
