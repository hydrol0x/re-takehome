import Mathlib
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases

/-- The least positive integer `n` such that `11` divides `3 ^ n - 1`.
Must be a numeric literal. -/
abbrev c07_answer : ℕ := 5

/-- `c07_answer` is the least element of the set of positive `n` with `11 ∣ 3 ^ n - 1`. -/
theorem c07_order_three :
    IsLeast {n : ℕ | 0 < n ∧ 11 ∣ 3 ^ n - 1} c07_answer := by
  -- 5 satisfies the condition
  have h5pos : (0 : ℕ) < 5 := by decide
  have h5div : 11 ∣ 3 ^ 5 - 1 := by norm_num
  have h5mem : (5 : ℕ) ∈ {n : ℕ | 0 < n ∧ 11 ∣ 3 ^ n - 1} := by
    exact ⟨h5pos, h5div⟩
  refine ⟨h5mem, ?_⟩
  intro n hn
  rcases hn with ⟨hnpos, hndiv⟩
  -- turn the divisibility into a congruence in `ZMod 11`
  have hmod : (3 : ZMod 11) ^ n = (1 : ZMod 11) := by
    have : (3 ^ n) ≡ 1 [MOD 11] := (Nat.modEq_iff_dvd).mpr hndiv
    exact (ZMod.eq_iff_modEq_nat).mpr this
  -- view `3` as a unit in `ZMod 11`
  let u : (ZMod 11)ˣ := Units.mk0 (3 : ZMod 11) (by decide)
  have hmod_u : (u : ZMod 11) ^ n = (1 : ZMod 11) := by
    simpa [u] using hmod
  have hpow_u : (u ^ n : (ZMod 11)ˣ) = 1 := by
    ext
    exact hmod_u
  -- the order of `u` is 5
  have horder : orderOf u = 5 := by
    norm_num
  -- from `hpow_u` we get that the order divides `n`
  have hdiv : orderOf u ∣ n :=
    (orderOf_dvd_iff_pow_eq_one (a := u) (n := n)).mpr hpow_u
  have h5dvd : 5 ∣ n := by
    simpa [horder] using hdiv
  exact Nat.le_of_dvd (by decide) h5dvd
