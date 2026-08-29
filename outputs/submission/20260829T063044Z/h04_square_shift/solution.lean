import Mathlib

theorem h04_square_shift (x y : ℕ) (hx : 0 < x) (hy : 0 < y) :
    x ^ 2 = y ^ 2 + 2 * y + 17 ↔ x = 5 ∧ y = 2 := by
  constructor
  · intro h
    -- Forward direction: from the equation, prove (x,y) = (5,2)
    have h1 : x ^ 2 = (y + 1) ^ 2 + 16 := by
      ring_nf at h ⊢
      exact h
    have h2 : x > y + 1 := by
      nlinarith
    set d := x - (y + 1) with hd
    have h3 : d > 0 := Nat.sub_pos_of_lt h2
    have h4 : d * (2 * y + 2 + d) = 16 := by
      have h5 : x = y + 1 + d := by
        rw [hd]
        omega
      rw [h5] at h1
      ring_nf at h1 ⊢
      omega
    -- Check each divisor of 16
    have h5 : d ∣ 16 := by
      use 2 * y + 2 + d
      omega
    have h6 : d ≤ 16 := Nat.le_of_dvd (by norm_num) h5
    interval_cases d <;> norm_num at h4 ⊢ <;>
      (try omega) <;>
      (try {
        have h7 : 2 * y + 2 + _ = _ := by omega
        omega
      })
  · rintro ⟨rfl, rfl⟩
    norm_num
