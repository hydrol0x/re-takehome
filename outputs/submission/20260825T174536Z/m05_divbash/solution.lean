import Mathlib
import Mathlib.Tactic.Omega

/-- If n = 1, then (n + 2) does not divide n^2 + 4. -/
lemma m05_helper_n1 (n : ℕ) (h : n = 1) : ¬(n + 2) ∣ n ^ 2 + 4 := by simp_all

/-- If n ≥ 2, then (n + 2) divides n^2 + 4 iff (n + 2) divides 8. -/
lemma m05_helper_ge2 (n : ℕ) (h : 2 ≤ n) : (n + 2) ∣ n ^ 2 + 4 ↔ (n + 2) ∣ 8 := by sorry

/-- If n ≥ 2, then (n + 2) divides 8 iff n = 2 or n = 6. -/
lemma m05_helper_8 (n : ℕ) (h : 2 ≤ n) : (n + 2) ∣ 8 ↔ n = 2 ∨ n = 6 := by sorry

/-- A positive integer `n` satisfies `(n + 2) ∣ n ^ 2 + 4` iff `n = 2` or `n = 6`. -/
theorem m05_divbash (n : ℕ) (hn : 0 < n) :
    (n + 2) ∣ n ^ 2 + 4 ↔ n = 2 ∨ n = 6 := by
  -- Case distinction: n is 1 or n is at least 2 (since n > 0)
  have h_cases : n = 1 ∨ 2 ≤ n := by
    omega
  
  cases h_cases with
  | inl h_eq_one =>
    -- Case n = 1
    -- Left side: (1 + 2) ∣ 1^2 + 4 ⟺ 3 ∣ 5 (False)
    have h_lhs_false : ¬(n + 2) ∣ n ^ 2 + 4 := m05_helper_n1 n h_eq_one
    -- Right side: n = 2 ∨ n = 6 ⟺ 1 = 2 ∨ 1 = 6 (False)
    have h_rhs_false : ¬(n = 2 ∨ n = 6) := by
      rw [h_eq_one]
      decide
    
    -- Equivalence of two false statements is true
    constructor
    · intro h_l
      exfalso
      exact h_lhs_false h_l
    · intro h_r
      exfalso
      exact h_rhs_false h_r
  | inr h_ge2 =>
    -- Case n ≥ 2
    -- Reduce LHS using helper 2
    have h_red : (n + 2) ∣ n ^ 2 + 4 ↔ (n + 2) ∣ 8 := m05_helper_ge2 n h_ge2
    -- Reduce intermediate condition using helper 3
    have h_sol : (n + 2) ∣ 8 ↔ n = 2 ∨ n = 6 := m05_helper_8 n h_ge2
    
    -- Chain the equivalences
    rw [h_red, h_sol]
