import Mathlib
import Mathlib.Tactic

open Nat

/-- The Diophantine equation `x^2 = y^2 + 2*y + 17` has the unique solution
`(x,y) = (5,2)` in positive natural numbers. -/
theorem h04_square_shift (x y : ℕ) (hx : 0 < x) (hy : 0 < y) :
    x ^ 2 = y ^ 2 + 2 * y + 17 ↔ x = 5 ∧ y = 2 := by
  constructor
  · intro h
    -- rewrite the right‑hand side as a shifted square
    have h' : x ^ 2 = (y + 1) ^ 2 + 16 := by
      have : y ^ 2 + 2 * y + 17 = (y + 1) ^ 2 + 16 := by ring
      simpa [this] using h
    -- subtract the squares
    have hfac : (x - (y + 1)) * (x + (y + 1)) = 16 := by
      have : x ^ 2 - (y + 1) ^ 2 = 16 := by
        have := congrArg (fun t => t - (y + 1) ^ 2) h'
        simpa [sub_eq, add_comm, add_left_comm, add_assoc] using this
      simpa [Nat.sq_sub_sq] using this
    -- set `a = x - (y+1)`, which is positive
    set a := x - (y + 1) with ha
    have ha_pos : 0 < a := by
      have : 0 < (x - (y + 1)) * (x + (y + 1)) := by
        simpa [hfac] using Nat.succ_pos 16
      exact Nat.pos_of_mul_pos_left this
    have hy1_lt_x : y + 1 < x := (Nat.sub_pos).mp ha_pos
    have hy1_le_x : y + 1 ≤ x := Nat.le_of_lt hy1_lt_x
    have hx_eq : x = (y + 1) + a := by
      have := Nat.sub_add_cancel hy1_le_x
      simpa [ha] using this.symm
    have hsum : x + (y + 1) = 2 * (y + 1) + a := by
      calc
        x + (y + 1) = ((y + 1) + a) + (y + 1) := by simpa [hx_eq]
        _ = (y + 1) + ((y + 1) + a) := by ac_rfl
        _ = 2 * (y + 1) + a := by ring
    -- rewrite the factorisation using `a`
    have hfac' : a * (2 * (y + 1) + a) = 16 := by
      simpa [ha, hsum] using hfac
    -- `a` divides `16`, hence `a ≤ 16`
    have hdiv : a ∣ 16 := ⟨2 * (y + 1) + a, by
      simpa [Nat.mul_comm] using hfac'⟩
    have ha_le : a ≤ 16 := Nat.le_of_dvd (Nat.succ_pos _) hdiv
    -- enumerate the possibilities for `a`
    have hcases : a = 1 ∨ a = 2 ∨ a = 4 ∨ a = 8 ∨ a = 16 := by
      have : a ∈ ({1, 2, 4, 8, 16} : Finset ℕ) := by
        have : a ∈ (Finset.range (16 + 1)).filter (fun n => n ∣ 16) := by
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_range.mpr (Nat.succ_le_of_lt ha_pos), hdiv⟩
        simpa [Finset.filter_eq, Finset.mem_range, Nat.lt_succ_iff,
               Finset.mem_insert, Finset.mem_singleton, Finset.mem_cons] using this
      rcases Finset.mem_insert.mp this with h | h
      · exact Or.inl h
      rcases Finset.mem_insert.mp h with h | h
      · exact Or.inr <| Or.inl h
      rcases Finset.mem_insert.mp h with h | h
      · exact Or.inr <| Or.inr <| Or.inl h
      rcases Finset.mem_insert.mp h with h | h
      · exact Or.inr <| Or.inr <| Or.inr <| Or.inl h
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr h
    -- solve each case
    rcases hcases with rfl | rfl | rfl | rfl | rfl
    · -- a = 1
      have : 1 * (2 * (y + 1) + 1) = 16 := hfac'
      have : 2 * (y + 1) + 1 = 16 := by simpa using this
      have : 2 * (y + 1) = 15 := by linarith
      have hy1 : y + 1 = 15 / 2 := by
        have : (2 : ℕ) ∣ 15 := by decide
        exact (Nat.mul_right_inj (Nat.succ_pos 1)).mp (by simpa [two_mul] using this)
      have : False := by decide
      exact (False.elim this)
    · -- a = 2
      have : 2 * (2 * (y + 1) + 2) = 16 := hfac'
      have : 2 * (y + 1) + 2 = 8 := by
        have : 2 ≠ 0 := by decide
        exact (Nat.mul_left_cancel this).mp (by simpa [two_mul] using this)
      have : 2 * (y + 1) = 6 := by linarith
      have hy1 : y + 1 = 3 := by
        exact (Nat.mul_right_inj (Nat.succ_pos 1)).mp (by simpa [two_mul] using this)
      have hy_eq : y = 2 := by linarith
      have hx_eq : x = 5 := by
        have : a = 2 := rfl
        have : x = (y + 1) + a := hx_eq
        simpa [hy_eq, this] using hx_eq
      exact ⟨by simpa [hx_eq], by simpa [hy_eq]⟩
    · -- a = 4
      have : 4 * (2 * (y + 1) + 4) = 16 := hfac'
      have : 2 * (y + 1) + 4 = 4 := by
        have : (4 : ℕ) ≠ 0 := by decide
        exact (Nat.mul_left_cancel this).mp (by simpa [two_mul] using this)
      have : 2 * (y + 1) = 0 := by linarith
      have : y + 1 = 0 := (Nat.mul_right_inj (Nat.succ_pos 1)).mp (by simpa [two_mul] using this)
      have : False := by decide
      exact (False.elim this)
    · -- a = 8
      have : 8 * (2 * (y + 1) + 8) = 16 := hfac'
      have : 2 * (y + 1) + 8 = 2 := by
        have : (8 : ℕ) ≠ 0 := by decide
        exact (Nat.mul_left_cancel this).mp (by simpa [two_mul] using this)
      have : 2 * (y + 1) = -6 := by linarith
      have : False := by decide
      exact (False.elim this)
    · -- a = 16
      have : 16 * (2 * (y + 1) + 16) = 16 := hfac'
      have : 2 * (y + 1) + 16 = 1 := by
        have : (16 : ℕ) ≠ 0 := by decide
        exact (Nat.mul_left_cancel this).mp (by simpa [two_mul] using this)
      have : 2 * (y + 1) = -15 := by linarith
      have : False := by decide
      exact (False.elim this)
  · rintro ⟨rfl, rfl⟩
    simp
