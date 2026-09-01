import Mathlib

/-- A positive integer `n` satisfies `(n + 2) ∣ n ^ 2 + 4` iff `n = 2` or `n = 6`. -/
theorem m05_divbash (n : ℕ) (hn : 0 < n) :
    (n + 2) ∣ n ^ 2 + 4 ↔ n = 2 ∨ n = 6 := by sorry

-- ============================================================================
-- Helper Lemmas
-- ============================================================================

lemma dvd_sub_of_le {a b c : ℕ} (h : a ∣ b) (h' : a ∣ c) (hle : c ≤ b) : 
    a ∣ b - c := by exact?

lemma square_expansion {n : ℕ} : (n + 2) ^ 2 = n ^ 2 + 4 * n + 4 := by linarith

lemma dvd_8_from_4n {n : ℕ} (h1 : n + 2 ∣ 4 * n) (h2 : n + 2 ∣ 4 * (n + 2)) : 
    n + 2 ∣ 8 := by exact?

lemma case_2 : (2 + 2) ∣ 2 ^ 2 + 4 := by norm_num

lemma case_6 : (6 + 2) ∣ 6 ^ 2 + 4 := by norm_num

lemma divisors_of_8 : {d : ℕ | d ∣ 8 ∧ 0 < d} = {1, 2, 4, 8} := by sorry

lemma no_dv_le_2 {d : ℕ} (hd : d ∣ 8) (hn : 0 < n) : d ≥ 3 → d ≠ 1 ∧ d ≠ 2 := by omega

lemma check_n_ge_3 {n : ℕ} (hn : 0 < n) : n + 2 ≥ 3 := by linarith

-- ============================================================================
-- Main Proof
-- ============================================================================

theorem m05_divbash_implies_cases {n : ℕ} (hn : 0 < n) (h : n + 2 ∣ n ^ 2 + 4) : 
    n = 2 ∨ n = 6 := by exact?

theorem m05_divbash_converse {n : ℕ} (hn : 0 < n) : 
    (n = 2 ∨ n = 6) → n + 2 ∣ n ^ 2 + 4 := by aesop
