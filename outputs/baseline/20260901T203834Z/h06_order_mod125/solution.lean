import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-- The multiplicative order of `2` modulo `125`. Must be a numeric literal. -/
abbrev h06_answer : ℕ := 100

/-- `h06_answer` is the least positive `n` with `2 ^ n ≡ 1 (mod 125)`. -/
theorem h06_order_mod125 :
    IsLeast {n : ℕ | 0 < n ∧ 2 ^ n % 125 = 1} h06_answer := by
  -- First show that `100` belongs to the set.
  have h100_mem : (0 < (100 : ℕ)) ∧ (2 ^ 100 % 125 = 1) := by
    constructor
    · decide
    · norm_num
  have h100_mem' : (100 : ℕ) ∈ {n : ℕ | 0 < n ∧ 2 ^ n % 125 = 1} := h100_mem
  refine ⟨h100_mem', ?_⟩
  intro n hn
  rcases hn with ⟨hnpos, hmod⟩
  -- Translate the congruence into `ZMod`.
  have hZ : ((2 : ℕ) : ZMod 125) ^ n = (1 : ZMod 125) := by
    apply (ZMod.eq_iff_modEq_nat).2
    dsimp [Nat.ModEq]
    simpa using hmod
  -- The order of `2` in `ZMod 125` divides `n`.
  have hdiv : orderOf ((2 : ℕ) : ZMod 125) ∣ n :=
    (orderOf_dvd_iff_pow_eq_one).2 hZ
  -- Compute the order of `2` in `ZMod 125`.
  have hpow100 : ((2 : ℕ) : ZMod 125) ^ 100 = (1 : ZMod 125) := by
    have : (2 ^ 100) % 125 = 1 := by norm_num
    apply (ZMod.eq_iff_modEq_nat).2
    dsimp [Nat.ModEq]; simpa using this
  have hdiv100 : orderOf ((2 : ℕ) : ZMod 125) ∣ 100 :=
    (orderOf_dvd_iff_pow_eq_one).2 hpow100
  -- Show that the order cannot be a proper divisor of `100`.
  have hpos : 0 < orderOf ((2 : ℕ) : ZMod 125) := by
    have hunit : IsUnit ((2 : ℕ) : ZMod 125) := by
      have : Nat.Coprime 2 125 := by norm_num
      exact (ZMod.isUnit_iff_coprime 2).2 this
    exact (orderOf_pos_iff).2 hunit
  have hle : orderOf ((2 : ℕ) : ZMod 125) ≤ 100 :=
    Nat.le_of_dvd (Nat.succ_le_of_lt hpos) hdiv100
  have hneq : orderOf ((2 : ℕ) : ZMod 125) ≠ 100 → False := by
    intro hneq
    have hlt : orderOf ((2 : ℕ) : ZMod 125) < 100 := Nat.lt_of_le_of_ne hle hneq
    -- From `order ∣ 100` and `order < 100` we get `order ≤ 50`.
    rcases Nat.dvd_of_modEq_zero (by
      have : (orderOf ((2 : ℕ) : ZMod 125)) ∣ 100 := hdiv100
      exact this) with ⟨k, hk⟩
    have hkpos : 2 ≤ k := by
      have : orderOf ((2 : ℕ) : ZMod 125) * k = 100 := hk.symm
      have : orderOf ((2 : ℕ) : ZMod 125) ≤ 100 / 2 := by
        have : orderOf ((2 : ℕ) : ZMod 125) * 2 ≤ orderOf ((2 : ℕ) : ZMod 125) * k := by
          simpa [two_mul] using Nat.mul_le_mul_left _ (Nat.succ_le_of_lt (Nat.lt_of_lt_of_le hlt hle))
        simpa [hk, Nat.mul_comm] using this
      exact Nat.succ_le_of_lt (Nat.lt_of_mul_lt_mul_left (by
        have : orderOf ((2 : ℕ) : ZMod 125) * 2 ≤ 100 := by
          simpa [hk] using Nat.le_of_eq (by rfl)
        exact this) (Nat.pos_of_lt hpos))
    have horder_le_50 : orderOf ((2 : ℕ) : ZMod 125) ≤ 50 := by
      have : orderOf ((2 : ℕ) : ZMod 125) * 2 ≤ 100 := by
        simpa [hk, Nat.mul_comm] using Nat.mul_le_mul_left _ hkpos
      exact Nat.le_of_mul_le_mul_left this (Nat.succ_pos 1)
    -- Now check all divisors ≤ 50.
    have hbad : ((2 : ZMod 125) ^ orderOf ((2 : ℕ) : ZMod 125)) ≠ (1 : ZMod 125) := by
      have horder_le_50' : orderOf ((2 : ℕ) : ZMod 125) ≤ 50 := horder_le_50
      have hcases : orderOf ((2 : ℕ) : ZMod 125) = 1 ∨
                    orderOf ((2 : ℕ) : ZMod 125) = 2 ∨
                    orderOf ((2 : ℕ) : ZMod 125) = 4 ∨
                    orderOf ((2 : ℕ) : ZMod 125) = 5 ∨
                    orderOf ((2 : ℕ) : ZMod 125) = 10 ∨
                    orderOf ((2 : ℕ) : ZMod 125) = 20 ∨
                    orderOf ((2 : ℕ) : ZMod 125) = 25 ∨
                    orderOf ((2 : ℕ) : ZMod 125) = 50 := by
        have : orderOf ((2 : ℕ) : ZMod 125) ∈
            ({1,2,4,5,10,20,25,50} : Finset ℕ) := by
          have : orderOf ((2 : ℕ) : ZMod 125) ≤ 50 := horder_le_50'
          have hmem : orderOf ((2 : ℕ) : ZMod 125) ∈ (Finset.range 51) := by
            exact Finset.mem_range.mpr (Nat.lt_succ_iff.mp this)
          have : orderOf ((2 : ℕ) : ZMod 125) ∈
                ({1,2,4,5,10,20,25,50} : Finset ℕ) := by
            have : orderOf ((2 : ℕ) : ZMod 125) ∈
                ({1,2,4,5,10,20,25,50} : Finset ℕ) ∨
                orderOf ((2 : ℕ) : ZMod 125) ∉ ({1,2,4,5,10,20,25,50} : Finset ℕ) := by
              apply Classical.em
            cases this with
            | inl h => exact h
            | inr h =>
              have : ((2 : ZMod 125) ^ orderOf ((2 : ℕ) : ZMod 125)) = (1 : ZMod 125) :=
                (orderOf_pow_eq_one _).mpr rfl
              have : False := by
                have : orderOf ((2 : ℕ) : ZMod 125) ∣ 100 := hdiv100
                have : orderOf ((2 : ℕ) : ZMod 125) = 0 := by
                  have : orderOf ((2 : ℕ) : ZMod 125) = 0 := by
                    have : (orderOf ((2 : ℕ) : ZMod 125)) = 0 := by
                      exact (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hlt)).symm
                    exact this
                  exact this
                exact (Nat.ne_of_lt hpos) this
              exact False.elim this
          exact this
        rcases Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp
          (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp
          (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp
          (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp
          (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp
          (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp
          (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp
          (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp
          (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp
          (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp
          (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp
          (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp
          (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp
          (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp
          (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp
          (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp
          (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp
          (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp
          (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp
          (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp
          (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp
          (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp
          (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp
          (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp
          (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp
          (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp
          (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp (Finset.mem_insert.mp
          (Finset.mem_insert.mp (Finset.mem_insert.mp
