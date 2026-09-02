import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

open Nat

/-- The only positive integer solution of  
    `y³ = x³ + 8·x² - 6·x + 8` is `x = 9 , y = 11`. -/
theorem rmo_2000_2
  (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
  (h : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8) :
  x = 9 ∧ y = 11 := by
  /- First we show that `x ≤ 9`. -/
  have hxle9 : x ≤ 9 := by
    by_contra hgt
    have h10 : 10 ≤ x := Nat.succ_le_of_lt (Nat.lt_of_not_ge hgt)
    have h9lt : 9 < x := Nat.lt_of_lt_of_le (by decide) h10
    /- For `x ≥ 10` the right‑hand side lies strictly between the consecutive cubes
        `(x+2)³` and `(x+3)³`. -/
    have hlow : (x + 2) ^ 3 < x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := by
      have : (x + 2) ^ 3 = x ^ 3 + 6 * x ^ 2 + 12 * x + 8 := by ring
      have : x ^ 3 + 8 * x ^ 2 - 6 * x + 8 =
          (x + 2) ^ 3 + (2 * x ^ 2 - 18 * x) := by ring
      have hpos : 0 < 2 * x ^ 2 - 18 * x := by
        have : 2 * x ^ 2 - 18 * x = 2 * x * (x - 9) := by ring
        have hxpos : 0 < x := hx
        have hsub : 0 < x - 9 := Nat.sub_pos_of_lt h9lt
        have : 0 < 2 * x * (x - 9) :=
          Nat.mul_pos (Nat.mul_pos (by decide) hx) hsub
        simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using this
      have : (x + 2) ^ 3 < (x + 2) ^ 3 + (2 * x ^ 2 - 18 * x) :=
        Nat.lt_add_of_pos_right _ hpos
      simpa [this] using this
    have hupp : x ^ 3 + 8 * x ^ 2 - 6 * x + 8 < (x + 3) ^ 3 := by
      have : (x + 3) ^ 3 = x ^ 3 + 9 * x ^ 2 + 27 * x + 27 := by ring
      have : x ^ 3 + 8 * x ^ 2 - 6 * x + 8 =
          (x + 3) ^ 3 - (x ^ 2 + 33 * x + 19) := by ring
      have hpos : 0 < x ^ 2 + 33 * x + 19 := Nat.succ_pos _
      have : (x + 3) ^ 3 - (x ^ 2 + 33 * x + 19) < (x + 3) ^ 3 :=
        Nat.sub_lt (Nat.le_of_lt hpos) (Nat.le_of_lt (Nat.succ_pos _))
      simpa [this] using this
    have hygt : x + 2 < y := by
      have : (x + 2) ^ 3 < y ^ 3 := by
        simpa [h] using hlow
      exact Nat.lt_of_pow_lt_pow this (by decide : 0 < 3)
    have hylt : y < x + 3 := by
      have : y ^ 3 < (x + 3) ^ 3 := by
        simpa [h] using hupp
      exact Nat.lt_of_pow_lt_pow this (by decide : 0 < 3)
    have hyle : y ≤ x + 2 := Nat.le_of_lt_succ hylt
    have : x + 2 < x + 2 := lt_of_lt_of_le hygt hyle
    exact (lt_irrefl _ this).elim
  /- Now `x ≤ 9`.  We check the finitely many possibilities. -/
  have hxpos : 0 < x := hx
  have : x = 9 := by
    interval_cases x using hxle9
    · -- case `x = 0` contradicts `hx`
      exact (Nat.lt_asymm hx (Nat.succ_le_iff.mp (Nat.zero_lt_one))).elim
    all_goals
      try
        { -- for `x = 1,…,8` we show the right‑hand side is not a perfect cube
          have hcalc : y ^ 3 = x ^ 3 + 8 * x ^ 2 - 6 * x + 8 := h
          norm_num at hcalc
          cases hcalc } }
    · -- case `x = 9`
      rfl
  subst this
  /- With `x = 9` the equation becomes `y³ = 1331 = 11³`. -/
  have hy_eq : y = 11 := by
    have : y ^ 3 = 1331 := by
      simpa [pow_three] using h
    have h11 : 11 ^ 3 = 1331 := by norm_num
    have : y ^ 3 = 11 ^ 3 := by simpa [h11] using this
    exact Nat.cube_eq_nat_iff_eq this
  exact ⟨rfl, hy_eq⟩
