import Mathlib

/-- A positive integer `n` satisfies `(n + 2) ∣ n ^ 2 + 4` iff `n = 2` or `n = 6`. -/
theorem m05_divbash (n : ℕ) (hn : 0 < n) :
    (n + 2) ∣ n ^ 2 + 4 ↔ n = 2 ∨ n = 6 := by
  constructor
  · -- Forward direction: (n + 2) ∣ n^2 + 4 → n = 2 ∨ n = 6
    intro h
    have h₁ : (n + 2) ∣ 4 * n := by sorry
    have h₂ : (n + 2) ∣ 8 := by sorry
    have h₃ : n ≤ 6 := by sorry
    have h₄ : n = 2 ∨ n = 6 := by sorry
    exact h₄
  · -- Backward direction: n = 2 ∨ n = 6 → (n + 2) ∣ n^2 + 4
    intro h
    cases h with
    | inl h =>
      rw [h]
      norm_num
    | inr h =>
      rw [h]
      norm_num

-- Helper lemmas for forward direction

/-- If (n + 2) ∣ n² + 4, then (n + 2) ∣ 4n -/
lemma div_4n (n : ℕ) (h : (n + 2) ∣ n ^ 2 + 4) : (n + 2) ∣ 4 * n := by sorry

/-- If (n + 2) ∣ 4n, then (n + 2) ∣ 8 -/
lemma div_8_from_4n (n : ℕ) (h : (n + 2) ∣ 4 * n) : (n + 2) ∣ 8 := by sorry

/-- If (n + 2) ∣ 8, then n ≤ 6 -/
lemma bound_n (n : ℕ) (h : (n + 2) ∣ 8) : n ≤ 6 := by sorry

/-- For 0 < n ≤ 6, if (n + 2) ∣ n² + 4, then n = 2 or n = 6 -/
lemma finite_check (n : ℕ) (hn : 0 < n) (hn_bound : n ≤ 6)
    (h : (n + 2) ∣ n ^ 2 + 4) : n = 2 ∨ n = 6 := by exact?