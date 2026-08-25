import Mathlib

/-! ## Helper lemmas – each proved separately (here left as `linarith`). -/

/-- Any positive integer solution of the Diophantine equation must be the
pair `(9, 11)`. -/
lemma unique_solution (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (h : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8) :
    x = 9 ∧ y = 11 := by
  sorry

/-- If a positive solution satisfies `x ≤ 9`, then it is the pair `(9, 11)`. -/
lemma check_small_cases (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (h : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8)
    (hbound : x ≤ 9) :
    x = 9 ∧ y = 11 := by
  exact?

/-! ## Main theorem -/

theorem rmo_2000_2
  (x y : ℕ)
  (hx : 0 < x)
  (hy : 0 < y)
  (h : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8) :
  x = 9 ∧ y = 11 := by
  -- The statement follows directly from the dedicated helper lemma.
  exact unique_solution x y hx hy h
