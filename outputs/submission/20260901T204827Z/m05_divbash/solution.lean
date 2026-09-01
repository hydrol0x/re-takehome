import Mathlib

/-- If a divides b and c ≤ b, then a divides b - c. -/
lemma dvd_sub_of_le {a b c : ℕ} (h : a ∣ b) (h' : a ∣ c) (hle : c ≤ b) : 
    a ∣ b - c := by exact?

/-- If (n+2) divides n²+4, then (n+2) divides 4n. -/
lemma dvd_implies_4n_divides {n : ℕ} (h : n + 2 ∣ n ^ 2 + 4) : 
    n + 2 ∣ 4 * n := by sorry

/-- For any n, (n+2)² = n² + 4n + 4. -/
lemma square_expansion {n : ℕ} : (n + 2) ^ 2 = n ^ 2 + 4 * n + 4 := by linarith

/-- If (n+2) divides 4n and (n+2) divides 4(n+2), then (n+2) divides 8. -/
lemma dvd_8_from_4n {n : ℕ} (h1 : n + 2 ∣ 4 * n) (h2 : n + 2 ∣ 4 * (n + 2)) : 
    n + 2 ∣ 8 := by exact?

/-- If n > 0 and n+2 divides 8, then n ≤ 6. -/
lemma bound_n_from_dvd_8 {n : ℕ} (hn : 0 < n) (h : n + 2 ∣ 8) : 
    n ≤ 6 := by sorry

/-- If n = 2, then (n+2) divides n²+4. -/
lemma case_2 : (2 + 2) ∣ 2 ^ 2 + 4 := by norm_num

/-- If n = 6, then (n+2) divides n²+4. -/
lemma case_6 : (6 + 2) ∣ 6 ^ 2 + 4 := by norm_num

/-- Positive divisors of 8 are 1, 2, 4, 8. -/
lemma divisors_of_8 : ∀ d : ℕ, d ∣ 8 ↔ d = 1 ∨ d = 2 ∨ d = 4 ∨ d = 8 := by sorry

/-- If n+2 divides 8 and n > 0, then n = 2 or n = 6. -/
lemma final_case_analysis {n : ℕ} (hn : 0 < n) (h : n + 2 ∣ 8) : 
    n = 2 ∨ n = 6 := by sorry

/-- A positive integer `n` satisfies `(n + 2) ∣ n ^ 2 + 4` iff `n = 2` or `n = 6`. -/
theorem m05_divbash (n : ℕ) (hn : 0 < n) :
    (n + 2) ∣ n ^ 2 + 4 ↔ n = 2 ∨ n = 6 := by
  constructor
  · intro h
    have h1 : n + 2 ∣ 4 * n := dvd_implies_4n_divides h
    have h2 : n + 2 ∣ 4 * (n + 2) := by norm_num
    have h3 : n + 2 ∣ 8 := dvd_8_from_4n h1 h2
    exact final_case_analysis hn h3
  · rintro (rfl | rfl)
    · exact case_2
    · exact case_6
