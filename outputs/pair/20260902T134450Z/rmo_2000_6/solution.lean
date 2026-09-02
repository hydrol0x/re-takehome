have h2 : 2 ∣ a * b := by
        have h2_div : 2 ∣ 2000 := by norm_num
        have h_ab_sq_b5 : 2 ∣ a ^ 2 * b ^ 5 := dvd_trans h2_div hdiv
        have h2_a_or_b : 2 ∣ a ∨ 2 ∣ b := by
          have : 2 ∣ a ^ 2 * b ^ 5 := h_ab_sq_b5
          have : 2 ∣ a ^ 2 ∨ 2 ∣ b ^ 5 := Nat.Prime.dvd_mul Nat.prime_two this
          cases this with
          | inl h => exact Or.inl (Nat.Prime.dvd_pow Nat.prime_two h)
          | inr h => exact Or.inr (Nat.Prime.dvd_pow Nat.prime_two h)
        cases h2_a_or_b with
        | inl h => exact dvd_mul_of_dvd_left h b
        | inr h => exact dvd_mul_of_dvd_right h a
