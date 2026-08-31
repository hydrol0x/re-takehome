import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Factorization
import Mathlib.Tactic

open Nat

theorem rmo_2000_6 :
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} 10) ∧
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} 20) := by
  constructor
  · -- first part
    refine ⟨?mem1, ?min1⟩
    · -- 10 belongs to the set
      refine ⟨1, 10, ?_, ?_, ?_, rfl⟩
      all_goals decide
    · intro n hn
      rcases hn with ⟨a, b, ha, hb, hdiv, rfl⟩
      have h2 : (2 : ℕ) ∣ a ^ 2 * b ^ 5 :=
        Nat.dvd_trans (by decide : (2 : ℕ) ∣ 2000) hdiv
      have h5 : (5 : ℕ) ∣ a ^ 2 * b ^ 5 :=
        Nat.dvd_trans (by decide : (5 : ℕ) ∣ 2000) hdiv
      have h2ab : (2 : ℕ) ∣ a * b := by
        rcases (Nat.prime_two.dvd_mul).1 (by
          simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using h2) with h2a | h2b
        ·
          have : (2 : ℕ) ∣ a := (Nat.prime_two.dvd_pow).1 h2a
          exact Nat.dvd_mul_of_dvd_left this b
        ·
          have : (2 : ℕ) ∣ b := (Nat.prime_two.dvd_pow).1 h2b
          exact Nat.dvd_mul_of_dvd_right this a
      have h5ab : (5 : ℕ) ∣ a * b := by
        rcases (Nat.prime_five.dvd_mul).1 (by
          simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using h5) with h5a | h5b
        ·
          have : (5 : ℕ) ∣ a := (Nat.prime_five.dvd_pow).1 h5a
          exact Nat.dvd_mul_of_dvd_left this b
        ·
          have : (5 : ℕ) ∣ b := (Nat.prime_five.dvd_pow).1 h5b
          exact Nat.dvd_mul_of_dvd_right this a
      have h10 : (10 : ℕ) ∣ a * b := by
        have : (Nat.lcm 2 5) ∣ a * b := (Nat.lcm_dvd_iff).2 ⟨h2ab, h5ab⟩
        simpa [Nat.lcm_eq_mul_of_coprime (Nat.coprime_prime_left Nat.prime_two)] using this
      have hpos : 0 < a * b := Nat.mul_pos ha hb
      exact Nat.le_of_dvd hpos h10
  · -- second part
    refine ⟨?mem2, ?min2⟩
    · -- 20 belongs to the set
      refine ⟨2, 10, ?_, ?_, ?_, rfl⟩
      all_goals decide
    · intro n hn
      rcases hn with ⟨a, b, ha, hb, hdiv, rfl⟩
      have h2 : (2 : ℕ) ∣ a ^ 3 * b ^ 4 :=
        Nat.dvd_trans (by decide : (2 : ℕ) ∣ 2000) hdiv
      have h5 : (5 : ℕ) ∣ a ^ 3 * b ^ 4 :=
        Nat.dvd_trans (by decide : (5 : ℕ) ∣ 2000) hdiv
      have h2ab : (2 : ℕ) ∣ a * b := by
        rcases (Nat.prime_two.dvd_mul).1 (by
          simpa [pow_three, pow_four, mul_comm, mul_left_comm, mul_assoc] using h2) with h2a | h2b
        ·
          have : (2 : ℕ) ∣ a := (Nat.prime_two.dvd_pow).1 h2a
          exact Nat.dvd_mul_of_dvd_left this b
        ·
          have : (2 : ℕ) ∣ b := (Nat.prime_two.dvd_pow).1 h2b
          exact Nat.dvd_mul_of_dvd_right this a
      have h5ab : (5 : ℕ) ∣ a * b := by
        rcases (Nat.prime_five.dvd_mul).1 (by
          simpa [pow_three, pow_four, mul_comm, mul_left_comm, mul_assoc] using h5) with h5a | h5b
        ·
          have : (5 : ℕ) ∣ a := (Nat.prime_five.dvd_pow).1 h5a
          exact Nat.dvd_mul_of_dvd_left this b
        ·
          have : (5 : ℕ) ∣ b := (Nat.prime_five.dvd_pow).1 h5b
          exact Nat.dvd_mul_of_dvd_right this a
      have h10 : (10 : ℕ) ∣ a * b := by
        have : (Nat.lcm 2 5) ∣ a * b := (Nat.lcm_dvd_iff).2 ⟨h2ab, h5ab⟩
        simpa [Nat.lcm_eq_mul_of_coprime (Nat.coprime_prime_left Nat.prime_two)] using this
      have hpos : 0 < a * b := Nat.mul_pos ha hb
      have h20 : (20 : ℕ) ∣ a * b := by
        rcases h2ab with ⟨c, hc⟩
        have : (5 : ℕ) ∣ c := by
          have : (5 : ℕ) ∣ a * b := h5ab
          rcases (Nat.prime_five.dvd_mul).1 (by
            simpa [hc, mul_comm, mul_left_comm, mul_assoc] using this) with h5c | h5d
          · exact h5c
          ·
            have : (5 : ℕ) ∣ 2 := by
              have : (5 : ℕ) ∣ 2 * c := by
                simpa [hc, mul_comm, mul_left_comm, mul_assoc] using h5ab
              exact (Nat.prime_five.not_dvd_one (by decide)).elim
            exact False.elim (Nat.not_lt.mpr (Nat.le_of_lt (by decide)) this)
        rcases this with ⟨d, hd⟩
        refine ⟨2 * d, ?_⟩
        simpa [hc, hd, mul_comm, mul_left_comm, mul_assoc] using rfl
      exact Nat.le_of_dvd hpos h20
