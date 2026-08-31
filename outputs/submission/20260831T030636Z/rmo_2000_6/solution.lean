import Mathlib.Data.Nat.Basic
import Mathlib.Order.Bounds.Basic

/-!
### Helper lemmas
-/

lemma factor_2000 : (2000 : ℕ) = 2 ^ 4 * 5 ^ 3 := by
  norm_num

-- case 1 witness: a = 1, b = 10, gives a * b = 10
lemma witness_case1 :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ a * b = 10 := by
  refine' ⟨1, 10, by decide, by decide, _, rfl⟩
  rw [factor_2000]
  norm_num

-- case 2 witness: a = 5, b = 2, gives a * b = 10
lemma witness_case2 :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ a * b = 10 := by
  refine' ⟨5, 2, by decide, by decide, _, rfl⟩
  rw [factor_2000]
  norm_num

-- lower bound for case 1: any positive a,b with 2000 ∣ a²·b⁵ satisfy a·b ≥ 10
lemma lower_bound_case1 (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hdiv : 2000 ∣ a ^ 2 * b ^ 5) : (10 : ℕ) ≤ a * b := by
  sorry

-- lower bound for case 2: any positive a,b with 2000 ∣ a³·b⁴ satisfy a·b ≥ 10
lemma lower_bound_case2 (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hdiv : 2000 ∣ a ^ 3 * b ^ 4) : (10 : ℕ) ≤ a * b := by
  sorry

/-!
### Main theorem
-/
theorem rmo_2000_6 :
    (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} 10) ∧
    (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} 10) := by
  constructor
  · -- first part
    refine ⟨?mem1, ?min1⟩
    · -- membership of 10
      rcases witness_case1 with ⟨a, b, ha, hb, hdiv, hprod⟩
      refine ⟨a, b, ha, hb, hdiv, ?_⟩
      symm
      exact hprod
    · -- minimality
      intro n hn
      rcases hn with ⟨a, b, ha, hb, hdiv, h_eq⟩
      have : (10 : ℕ) ≤ a * b := lower_bound_case1 a b ha hb hdiv
      simpa [h_eq] using this
  · -- second part
    refine ⟨?mem2, ?min2⟩
    · -- membership of 10
      rcases witness_case2 with ⟨a, b, ha, hb, hdiv, hprod⟩
      refine ⟨a, b, ha, hb, hdiv, ?_⟩
      symm
      exact hprod
    · -- minimality
      intro n hn
      rcases hn with ⟨a, b, ha, hb, hdiv, h_eq⟩
      have : (10 : ℕ) ≤ a * b := lower_bound_case2 a b ha hb hdiv
      simpa [h_eq] using this
