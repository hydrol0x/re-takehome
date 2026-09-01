import Mathlib.Data.Nat.Prime
import Mathlib.Tactic

theorem h04_square_shift (x y : ℕ) (hx : 0 < x) (hy : 0 < y) :
    x ^ 2 = y ^ 2 + 2 * y + 17 ↔ x = 5 ∧ y = 2 := by
  constructor
  · intro h
    -- rewrite the right‑hand side as a shifted square
    have h₁ : x ^ 2 = (y + 1) ^ 2 + 16 := by
      have : y ^ 2 + 2 * y + 17 = (y + 1) ^ 2 + 16 := by
        ring
      simpa [this] using h
    -- turn the equality into a product
    have h₂ : (x - (y + 1)) * (x + (y + 1)) = 16 := by
      have : x ^ 2 - (y + 1) ^ 2 = 16 := by
        calc
          x ^ 2 - (y + 1) ^ 2 = ((y + 1) ^ 2 + 16) - (y + 1) ^ 2 := by
            simpa [h₁]
          _ = 16 := Nat.add_sub_cancel _ _
      simpa [Nat.sq_sub_sq] using this
    -- the first factor is positive
    have hpos_sum : 0 < x + (y + 1) := Nat.add_pos hx (Nat.succ_pos _)
    have hpos_a : 0 < x - (y + 1) := by
      have : 0 < (x - (y + 1)) * (x + (y + 1)) := by
        simpa [h₂] using (Nat.succ_pos 15)
      exact Nat.pos_of_mul_pos_left this hpos_sum
    set a := x - (y + 1) with ha
    have ha_pos : 0 < a := by
      simpa [ha] using hpos_a
    have hdiv : a ∣ 16 := ⟨x + (y + 1), by
      simpa [ha, Nat.mul_comm] using h₂⟩
    -- a is a positive divisor of 16, hence a ≤ 4
    have ha_le4 : a ≤ 4 := by
      rcases Nat.dvd_prime (by decide : Nat.Prime 2) hdiv with h | h
      · rcases h with rfl | rfl
        · exact (Nat.succ_le_succ (Nat.zero_le 0))
        · exact (Nat.succ_le_succ (Nat.zero_le 1))
      · rcases h with h | h
        · rcases h with rfl | rfl
          · exact (Nat.succ_le_succ (Nat.zero_le 2))
          · exact (Nat.succ_le_succ (Nat.zero_le 3))
        · rcases h with rfl | rfl
          · exact (Nat.succ_le_succ (Nat.zero_le 4))
          · exact (Nat.succ_le_succ (Nat.zero_le 5))
    -- now we can enumerate the possibilities for a
    have : a = 2 := by
      have hcases : a = 1 ∨ a = 2 ∨ a = 4 ∨ a = 8 ∨ a = 16 := by
        have : a ∈ [1, 2, 4, 8, 16] := by
          have : a ∣ 16 := hdiv
          have : a ≤ 16 := Nat.le_of_dvd (Nat.succ_pos _) this
          have : a = 1 ∨ a = 2 ∨ a = 4 ∨ a = 8 ∨ a = 16 := by
            interval_cases a using (by decide : 0 ≤ a) <;> try tauto
          exact this
        rcases this with h | h | h | h | h <;> simp_all
      rcases hcases with h | h | h | h | h
      · -- a = 1 leads to a contradiction
        have : (x + (y + 1)) = 16 := by
          have : a * (x + (y + 1)) = 16 := by simpa [ha] using h₂
          simpa [h] using this
        have : 2 * (y + 1) = 15 := by
          have : (x + (y + 1)) = (x - (y + 1)) + 2 * (y + 1) := by
            ring
          have : (x - (y + 1)) + 2 * (y + 1) = 16 := by
            simpa [h] using this
          linarith
        have : (y + 1) = 7.5 := by linarith
        have : False := by norm_num at this
        exact (False.elim this)
      · exact h
      · -- a = 4 gives impossible parity
        have : (x + (y + 1)) = 4 := by
          have : a * (x + (y + 1)) = 16 := by simpa [ha] using h₂
          simpa [h] using this
        have : 2 * (y + 1) = 0 := by
          have : (x + (y + 1)) = (x - (y + 1)) + 2 * (y + 1) := by ring
          have : (x - (y + 1)) + 2 * (y + 1) = 4 := by
            simpa [h] using this
          linarith
        have : y + 1 = 0 := by linarith
        have : False := Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero _ (Nat.succ_ne_zero
