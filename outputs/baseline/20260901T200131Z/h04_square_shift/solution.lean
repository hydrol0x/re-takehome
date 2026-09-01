import Mathlib

theorem h04_square_shift (x y : ℕ) (hx : 0 < x) (hy : 0 < y) :
    x ^ 2 = y ^ 2 + 2 * y + 17 ↔ x = 5 ∧ y = 2 := by
  constructor
  · -- Forward direction: if x^2 = y^2 + 2*y + 17, then x = 5 and y = 2
    intro h
    have h1 : x ^ 2 = (y + 1) ^ 2 + 16 := by
      calc
        x ^ 2 = y ^ 2 + 2 * y + 17 := h
        _ = (y + 1) ^ 2 + 16 := by
          ring_nf
          <;> simp [Nat.pow_succ, Nat.mul_succ]
          <;> ring_nf
    have h2 : x ^ 2 - (y + 1) ^ 2 = 16 := by
      have h3 : (y + 1) ^ 2 + 16 ≤ x ^ 2 := by
        omega
      omega
    have h3 : (x - (y + 1)) * (x + (y + 1)) = 16 := by
      have h4 : x ≥ y + 1 := by
        by_contra h5
        have h6 : x < y + 1 := by omega
        have h7 : x ^ 2 < (y + 1) ^ 2 := by
          exact Nat.pow_lt_pow_of_lt_left h6 (by omega)
        omega
      have h5 : x ^ 2 - (y + 1) ^ 2 = (x - (y + 1)) * (x + (y + 1)) := by
        have h6 : x ≥ y + 1 := h4
        have h7 : x ^ 2 ≥ (y + 1) ^ 2 := by
          exact Nat.pow_le_pow_of_le_left h6 2
        rw [← Nat.sub_sub_self h7]
        rw [Nat.sub_sub_self h7]
        ring_nf
        <;> simp [Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib, Nat.add_assoc]
        <;> ring_nf at *
        <;> omega
      rw [h5] at h2
      exact h2
    -- Now we know (x - (y + 1)) * (x + (y + 1)) = 16
    -- Since x, y > 0, we have x + (y + 1) > x - (y + 1)
    -- And both factors must be positive divisors of 16
    have h4 : x - (y + 1) = 2 ∧ x + (y + 1) = 8 := by
      have h5 : x - (y + 1) > 0 := by
        by_contra h6
        have h7 : x - (y + 1) = 0 := by omega
        have h8 : (x - (y + 1)) * (x + (y + 1)) = 0 := by
          rw [h7]
          simp
        omega
      have h6 : x - (y + 1) ≤ x + (y + 1) := by
        omega
      have h7 : x - (y + 1) ∣ 16 := by
        use x + (y + 1)
        linarith
      have h8 : x - (y + 1) ∈ ({1, 2, 4, 8, 16} : Set ℕ) := by
        have h9 : x - (y + 1) ∣ 16 := h7
        have h10 : x - (y + 1) ≠ 0 := by omega
        have h11 : x - (y + 1) ≤ 16 := by
          have h12 : x - (y + 1) * (x + (y + 1)) = 16 := by linarith
          have h13 : x - (y + 1) ≤ 16 := by
            by_contra h14
            have h15 : x - (y + 1) ≥ 17 := by omega
            have h16 : x + (y + 1) ≥ 1 := by omega
            have h17 : (x - (y + 1)) * (x + (y + 1)) ≥ 17 * 1 := by
              nlinarith
            omega
          exact h13
        interval_cases x - (y + 1) <;> norm_num at h9 ⊢ <;> try omega
      rcases h8 with (h8 | h8 | h8 | h8 | h8)
      · -- Case: x - (y + 1) = 1
        have h9 : x + (y + 1) = 16 := by
          have h10 : (x - (y + 1)) * (x + (y + 1)) = 16 := by linarith
          rw [h8] at h10
          omega
        have h10 : 2 * x = 17 := by
          have h11 : x - (y + 1) = 1 := h8
          have h12 : x + (y + 1) = 16 := h9
          omega
        omega
      · -- Case: x - (y + 1) = 2
        have h9 : x + (y + 1) = 8 := by
          have h10 : (x - (y + 1)) * (x + (y + 1)) = 16 := by linarith
          rw [h8] at h10
          omega
        have h10 : 2 * x = 10 := by
          have h11 : x - (y + 1) = 2 := h8
          have h12 : x + (y + 1) = 8 := h9
          omega
        have h11 : x = 5 := by omega
        have h12 : y = 2 := by
          have h13 : x - (y + 1) = 2 := h8
          rw [h11] at h13
          omega
        exact ⟨by omega, by omega⟩
      · -- Case: x - (y + 1) = 4
        have h9 : x + (y + 1) = 4 := by
          have h10 : (x - (y + 1)) * (x + (y + 1)) = 16 := by linarith
          rw [h8] at h10
          omega
        have h10 : 2 * (y + 1) = 0 := by
          have h11 : x - (y + 1) = 4 := h8
          have h12 : x + (y + 1) = 4 := h9
          omega
        omega
      · -- Case: x - (y + 1) = 8
        have h9 : x + (y + 1) = 2 := by
          have h10 : (x - (y + 1)) * (x + (y + 1)) = 16 := by linarith
          rw [h8] at h10
          omega
        omega
      · -- Case: x - (y + 1) = 16
        have h9 : x + (y + 1) = 1 := by
          have h10 : (x - (y + 1)) * (x + (y + 1)) = 16 := by linarith
          rw [h8] at h10
          omega
        omega
    have h5 : x = 5 := by
      have h6 : x - (y + 1) = 2 := h4.1
      have h7 : x + (y + 1) = 8 := h4.2
      omega
    have h6 : y = 2 := by
      have h7 : x - (y + 1) = 2 := h4.1
      have h8 : x + (y + 1) = 8 := h4.2
      omega
    exact ⟨h5, h6⟩
  · -- Backward direction: if x = 5 and y = 2, then x^2 = y^2 + 2*y + 17
    rintro ⟨rfl, rfl⟩
    norm_num
