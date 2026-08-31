import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

open Nat

/-- Helper: the remainder of `2 ^ n` modulo `7` depends only on `n % 3`. -/
lemma pow_two_mod_seven (n : ℕ) :
    (2 ^ n) % 7 = match n % 3 with
      | 0 => 1
      | 1 => 2
      | 2 => 4
      | _ => 0 := by
  have hlt : n % 3 < 3 := Nat.mod_lt _ (by decide)
  rcases Nat.mod_eq_of_lt hlt with rfl
  cases h : n % 3 with
  | zero =>
      simp [h] at *
  | succ r =>
      cases r with
      | zero =>
          simp [h] at *
      | succ r =>
          have : r = 0 := by
            have : n % 3 ≤ 2 := Nat.le_of_lt_succ hlt
            have : r.succ.succ ≤ 2 := by
              simpa [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
            exact Nat.le_antisymm (Nat.succ_le_of_lt (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_one)))) this
          subst this
          simp [h] at *

/-- IMO 1964 P1 (a): `7 ∣ 2 ^ n - 1` iff `3 ∣ n`, for positive `n`. -/
theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  have hmod : (2 ^ n) % 7 = 1 ↔ n % 3 = 0 := by
    have := pow_two_mod_seven n
    rcases Nat.mod_lt n (by decide : 0 < 3) with hlt
    have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by
      have : n % 3 ≤ 2 := Nat.le_of_lt_succ hlt
      interval_cases (n % 3) using this
    rcases hcases with h0 | h1 | h2
    · subst h0
      simp [pow_two_mod_seven] at *
    · subst h1
      simp [pow_two_mod_seven] at *
    · subst h2
      simp [pow_two_mod_seven] at *
  have hdiv : (7 ∣ 2 ^ n - 1) ↔ (2 ^ n) % 7 = 1 := by
    constructor
    · intro h
      have : (2 ^ n - 1) % 7 = 0 := Nat.mod_eq_zero_of_dvd h
      have : (2 ^ n) % 7 = 1 := by
        have : (2 ^ n) % 7 = ((2 ^ n - 1) + 1) % 7 := by
          simpa [Nat.add_sub_cancel] using rfl
        simpa [Nat.mod_add_mod, this, Nat.mod_one] using this
      exact this
    · intro h
      have : (2 ^ n - 1) % 7 = 0 := by
        have : (2 ^ n) % 7 = 1 := h
        have : ((2 ^ n) - 1) % 7 = ((2 ^ n) % 7 - 1 % 7) % 7 := by
          simpa [Nat.sub_mod] using rfl
        simpa [this, h, Nat.mod_one] using rfl
      exact Nat.dvd_of_mod_eq_zero this
  have : (7 ∣ 2 ^ n - 1) ↔ n % 3 = 0 := by
    simpa [hdiv] using hmod
  simpa [Nat.dvd_iff_modEq_zero] using this

/-- IMO 1964 P1 (b): no positive `n` has `7 ∣ 2 ^ n + 1`. -/
theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  intro h
  have hmod : (2 ^ n) % 7 = 6 := by
    have : (2 ^ n + 1) % 7 = 0 := Nat.mod_eq_zero_of_dvd h
    have : ((2 ^ n) % 7 + 1 % 7) % 7 = 0 := by
      simpa [Nat.add_mod, Nat.mod_one] using this
    have : (2 ^ n) % 7 = 6 := by
      have : (2 ^ n) % 7 + 1 = 7 := by
        have : (2 ^ n) % 7 + 1 < 8 := Nat.lt_succ_of_le (Nat.le_of_lt_succ (Nat.mod_lt _ (by decide)))
        have : (2 ^ n) % 7 + 1 = 7 := Nat.mod_eq_of_lt (by decide) this
        exact this
      simpa [Nat.mod_eq_of_lt (by decide)] using this
    exact this
  have hcases : (2 ^ n) % 7 = 1 ∨ (2 ^ n) % 7 = 2 ∨ (2 ^ n) % 7 = 4 := by
    have := pow_two_mod_seven n
    rcases Nat.mod_lt n (by decide : 0 < 3) with hlt
    interval_cases (n % 3) using (Nat.le_of_lt_succ hlt)
    all_goals
      simp [pow_two_mod_seven] at *
  rcases hcases with h1 | h2 | h4
  all_goals
    have : (2 ^ n) % 7 ≠ 6 := by
      norm_num at *
    exact this
