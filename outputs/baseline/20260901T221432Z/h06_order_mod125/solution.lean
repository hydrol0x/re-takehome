import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

open Nat

/-- The multiplicative order of `2` modulo `125`. Must be a numeric literal. -/
abbrev h06_answer : ℕ := 100

/-- `h06_answer` is the least positive `n` with `2 ^ n ≡ 1 (mod 125)`. -/
theorem h06_order_mod125 :
    IsLeast {n : ℕ | 0 < n ∧ 2 ^ n % 125 = 1} h06_answer := by
  -- `100` satisfies the condition
  have hmem : (0 < (100 : ℕ)) ∧ 2 ^ 100 % 125 = 1 := by
    constructor
    · decide
    · norm_num
  refine ⟨by
    simpa [h06_answer] using hmem, ?_⟩
  intro n hn
  rcases hn with ⟨hnpos, hmodn⟩
  -- turn the congruence into an equality in `ZMod 125`
  have hmodZ : ((2 : ZMod 125) ^ n) = (1 : ZMod 125) := by
    apply (ZMod.eq_iff_modEq_nat).2
    dsimp [Nat.ModEq]
    simpa using hmodn
  -- the order of `2` in `ZMod 125` divides any exponent giving `1`
  have hdiv : (orderOf (2 : ZMod 125)) ∣ n :=
    (orderOf_dvd_iff_pow_eq_one (a := (2 : ZMod 125)) (n := n)).mpr hmodZ
  -- compute the order (it is `100`)
  have horder_eq : orderOf (2 : ZMod 125) = 100 := by
    norm_num
  -- the order is positive
  have horder_pos : 0 < orderOf (2 : ZMod 125) :=
    orderOf_pos (a := (2 : ZMod 125))
  -- hence it is ≤ any such exponent
  have hle : orderOf (2 : ZMod 125) ≤ n :=
    Nat.le_of_dvd horder_pos hdiv
  simpa [horder_eq] using hle
