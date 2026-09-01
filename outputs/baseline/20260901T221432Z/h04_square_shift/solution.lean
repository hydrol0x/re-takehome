import Mathlib.Tactic
open Nat

/-- The only positive integer solution of `x^2 = y^2 + 2*y + 17` is `(x,y) = (5,2)`. -/
theorem h04_square_shift (x y : ℕ) (hx : 0 < x) (hy : 0 < y) :
    x ^ 2 = y ^ 2 + 2 * y + 17 ↔ x = 5 ∧ y = 2 := by
  constructor
  · intro h
    -- rewrite the right‑hand side as a shifted square
    have h₁ : x ^ 2 = (y + 1) ^ 2 + 16 := by
      have : y ^ 2 + 2 * y + 17 = (y + 1) ^ 2 + 16 := by ring
      simpa [this] using h
    -- set `a = x - y`
    have hle : y ≤ x := by
      have : (y + 1) ^ 2 < x ^ 2 := by
        have : (y + 1) ^ 2 + 16 = x ^ 2 := by
          simpa [add_comm, add_left_comm, add_assoc] using h₁.symm
        have : (y + 1) ^ 2 < (y + 1) ^ 2 + 16 :=
          Nat.lt_add_of_pos_right _ (by decide)
        simpa [this] using congrArg (fun t : ℕ => t) this
      exact le_of_lt_succ (Nat.lt_of_pow_lt_pow (Nat.succ_pos _) this)
    set a := x - y with ha
    have hx_eq : x = a + y := by
      have : y + a = x := (Nat.add_sub_of_le hle).symm
      simpa [add_comm] using this
    have ha_pos : 0 < a := by
      have : y < x := lt_of_le_of_ne hle (by
        intro h_eq; have : x ^ 2 = y ^ 2 := by simpa [h_eq] using h
        exact (Nat.pow_inj_iff (Nat.succ_pos _) (Nat.succ_pos _)).mp this)
      exact Nat.sub_pos_of_lt this
    -- translate the original equation using `a`
    have h₂ : a ^ 2 + (2 * a - 2) * y = 17 := by
      have : (a + y) ^ 2 = y ^ 2 + 2 * y + 17 := by
        simpa [hx_eq] using h
      have : a ^ 2 + 2 * a * y + y ^ 2 = y ^ 2 + 2 * y + 17 := by
        simpa [pow_two, mul_add, add_comm, add_left_comm, add_assoc, mul_comm,
               mul_left_comm, mul_assoc, Nat.add_sub_cancel] using this
      have : a ^ 2 + 2 * a * y = 2 * y + 17 := by
        simpa [add_comm, add_left_comm, add_assoc] using this
      have : a ^ 2 + (2 * a - 2) * y = 17 := by
        have h3 : (2 * a - 2) * y = 2 * a * y - 2 * y := by
          ring
        have h4 : a ^ 2 + 2 * a * y - (2 * y) = 17 := by
          simpa [sub_eq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
            (eq_sub_of_add_eq (a ^ 2 + 2 * a * y) (2 * y) this).symm
        simpa [h3, sub_eq, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h4
      exact this
    -- from the last equality we get a bound on `a`
    have a_le_four : a ≤ 4 := by
      have : a ^ 2 ≤ 17 := by
        have : (2 * a - 2) * y ≥ 0 := Nat.mul_nonneg (Nat.sub_nonneg_of_le (Nat.le_of_lt (Nat.succ_lt_succ (Nat.succ_pos _)))) (Nat.zero_le _)
        have : a ^ 2 ≤ a ^ 2 + (2 * a - 2) * y := Nat.le_add_right _ _
        have : a ^ 2 ≤ 17 := le_trans this (by simpa [h₂])
        exact this
      exact Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (Nat.lt_of_pow_lt_pow (Nat.succ_pos _) (by
        have : a ^ 2 ≤ 17 := this
        have : a ≤ 5 := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (Nat.lt_of_pow_lt_pow (Nat.succ_pos _) (by
          have : (a : ℕ) ^ 2 ≤ 17 := this
          exact this)) (by decide)))
        ) (by decide))
    have a_cases : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by
      have : a ≤ 4 := a_le_four
      interval_cases a using this <;> first
        | left; exact ?_ | right; exact ?_
    rcases a_cases with h1 | h2 | h3 | h4
    · -- a = 1 leads to contradiction
      have : (1 : ℕ) ^ 2 + (2 * 1 - 2) * y = 17 := by simpa [h1] using h₂
      norm_num at this
    · -- a = 2 leads to contradiction
      have : (2 : ℕ) ^ 2 + (2 * 2 - 2) * y = 17 := by simpa [h2] using h₂
      have : 4 + 2 * y = 17 := by simpa [mul_comm, mul_left_comm, mul_assoc] using this
      have : 2 * y = 13 := by linarith
      have : y = 13 / 2 := Nat.eq_of_mul_eq_mul_left (Nat.succ_pos _) (by simpa using this)
      have : False := by decide
      exact False.elim this
    · -- a = 3 gives the solution
      have : (3 : ℕ) ^ 2 + (2 * 3 - 2) * y = 17 := by simpa [h3] using h₂
      have : 9 + 4 * y = 17 := by simpa [mul_comm, mul_left_comm, mul_assoc] using this
      have : 4 * y = 8 := by linarith
      have hy2 : y = 2 := by
        have : 0 < 4 := by decide
        exact (Nat.mul_right_injective (Nat.succ_pos _)).mp this
      have hx5 : x = 5 := by
        have : a = 3 := h3
        have : x = a + y := hx_eq
        simpa [this, hy2] using this
      exact ⟨hx5, hy2⟩
    · -- a = 4 leads to contradiction
      have : (4 : ℕ) ^ 2 + (2 * 4 - 2) * y = 17 := by simpa [h4] using h₂
      have : 16 + 6 * y = 17 := by simpa [mul_comm, mul_left_comm, mul_assoc] using this
      have : 6 * y = 1 := by linarith
      have : False := by decide
      exact False.elim this
  · rintro ⟨rfl, rfl⟩
    norm_num
