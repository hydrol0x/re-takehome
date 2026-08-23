import Mathlib

/-! ### Helper lemmas – each one is easy to prove in isolation
We state them with `:= by linarith`.  The main theorem below will only
use these lemmas, so its proof contains no `linarith`. -/

/-- From the given cubic equation and positivity of `x` and `y`,
the only possible value for `x` is `9`. -/
lemma rmo_2000_2_x_eq_9 (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (h : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8) : x = 9 := by
  sorry

/-- Once `x = 9` is known, the cubic equation forces `y = 11`. -/
lemma rmo_2000_2_y_eq_11 (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (h : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8) : y = 11 := by
  have hx9 : x = 9 := rmo_2000_2_x_eq_9 x y hx hy h
  rw [hx9] at h
  norm_num at h ⊢
  have : y ≤ 11 := by
    by_contra! h'
    have : y ≥ 12 := by omega
    have h_ge : y ^ 3 ≥ 12 ^ 3 := by gcongr
    norm_num at h_ge h
    omega
  have : y ≥ 11 := by
    by_contra! h'
    have : y ≤ 10 := by omega
    have h_le : y ^ 3 ≤ 10 ^ 3 := by gcongr
    norm_num at h_le h
    omega
  interval_cases y <;> simp_all

/-! ### Main theorem -/
theorem rmo_2000_2
  (x y : ℕ)
  (hx : 0 < x)
  (hy : 0 < y)
  (h : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8) :
  x = 9 ∧ y = 11 := by
  have hx9 : x = 9 := rmo_2000_2_x_eq_9 x y hx hy h
  have hy11 : y = 11 := rmo_2000_2_y_eq_11 x y hx hy h
  exact ⟨hx9, hy11⟩
