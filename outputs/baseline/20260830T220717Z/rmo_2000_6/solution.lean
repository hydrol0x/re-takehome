import Mathlib.Data.Nat.Basic
import Mathlib.Order.Bounds.Basic

open Nat

theorem rmo_2000_6 :
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} 10) ∧
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} 10) := by
  constructor
  · -- first part
    refine ⟨?mem1, ?least1⟩
    · -- 10 belongs to the set
      refine ⟨1, 10, ?pos1, ?pos2, ?dvd1, ?eq⟩
      all_goals decide
      · -- 2000 ∣ 1^2 * 10^5
        have : (2000 : ℕ) ∣ 10 ^ 5 := by
          refine ⟨50, ?_⟩
          simp
        simpa using this
      · -- equality
        simp
    · -- minimality
      intro n hn
      rcases hn with ⟨a, b, ha, hb, hdiv, rfl⟩
      -- 2 divides a * b
      have h2ab : (2 : ℕ) ∣ a * b := by
        have h2pow : (2 : ℕ) ∣ a ^ 2 * b ^ 5 :=
          Nat.dvd_trans (by decide : (2 : ℕ) ∣ 2000) hdiv
        rcases (Nat.prime_two.dvd_mul).1 h2pow with h2a | h2b
        · have h2a' : (2 : ℕ) ∣ a := (Nat.prime_two.dvd_pow).1 h2a
          exact Nat.dvd_mul_of_dvd_left h2a' b
        · have h2b' : (2 : ℕ) ∣ b := (Nat.prime_two.dvd_pow).1 h2b
          exact Nat.dvd_mul_of_dvd_right h2b' a
      -- 5 divides a * b
      have h5ab : (5 : ℕ) ∣ a * b := by
        have h5pow : (5 : ℕ) ∣ a ^ 2 * b ^ 5 :=
          Nat.dvd_trans (by decide : (5 : ℕ) ∣ 2000) hdiv
        rcases (Nat.prime_five.dvd_mul).1 h5pow with h5a | h5b
        · have h5a' : (5 : ℕ) ∣ a := (Nat.prime_five.dvd_pow).1 h5a
          exact Nat.dvd_mul_of_dvd_left h5a' b
        · have h5b' : (5 : ℕ) ∣ b := (Nat.prime_five.dvd_pow).1 h5b
          exact Nat.dvd_mul_of_dvd_right h5b' a
      -- combine to get 10 ∣ a * b
      rcases h2ab with ⟨k, hk⟩
      rcases h5ab with ⟨l, hl⟩
      have h5k : (5 : ℕ) ∣ k := by
        have : (5 : ℕ) ∣ 2 * k := by
          simpa [hk] using hl
        have hcop : Nat.Coprime (5) (2) :=
          (Nat.coprime_comm).1 (Nat.coprime_two_left 5)
        exact (Nat.Coprime.dvd_of_dvd_mul_left hcop) this
      rcases h5k with ⟨m, hm⟩
      have h10ab : (10 : ℕ) ∣ a * b := by
        refine ⟨10 * m, ?_⟩
        calc
          a * b = 2 * k := hk
          _ = 2 * (5 * m) := by simpa [hm]
          _ = 10 * m := by ring
      have hpos : 0 < a * b := Nat.mul_pos ha hb
      exact Nat.le_of_dvd hpos h10ab
  · -- second part
    refine ⟨?mem2, ?least2⟩
    · -- 10 belongs to the second set
      refine ⟨1, 10, ?pos1, ?pos2, ?dvd2, ?eq⟩
      all_goals decide
      · -- 2000 ∣ 1^3 * 10^4
        have : (2000 : ℕ) ∣ 10 ^ 4 := by
          refine ⟨5, ?_⟩
          simp
        simpa using this
      · simp
    · -- minimality
      intro n hn
      rcases hn with ⟨a, b, ha, hb, hdiv, rfl⟩
      -- 2 divides a * b
      have h2ab : (2 : ℕ) ∣ a * b := by
        have h2pow : (2 : ℕ) ∣ a ^ 3 * b ^ 4 :=
          Nat.dvd_trans (by decide : (2 : ℕ) ∣ 2000) hdiv
        rcases (Nat.prime_two.dvd_mul).1 h2pow with h2a | h2b
        · have h2a' : (2 : ℕ) ∣ a := (Nat.prime_two.dvd_pow).1 h2a
          exact Nat.dvd_mul_of_dvd_left h2a' b
        · have h2b' : (2 : ℕ) ∣ b := (Nat.prime_two.dvd_pow).1 h2b
          exact Nat.dvd_mul_of_dvd_right h2b' a
      -- 5 divides a * b
      have h5ab : (5 : ℕ) ∣ a * b := by
        have h5pow : (5 : ℕ) ∣ a ^ 3 * b ^ 4 :=
          Nat.dvd_trans (by decide : (5 : ℕ) ∣ 2000) hdiv
        rcases (Nat.prime_five.dvd_mul).1 h5pow with h5a | h5b
        · have h5a' : (5 : ℕ) ∣ a := (Nat.prime_five.dvd_pow).1 h5a
          exact Nat.dvd_mul_of_dvd_left h5a' b
        · have h5b' : (5 : ℕ) ∣ b := (Nat.prime_five.dvd_pow).1 h5b
          exact Nat.dvd_mul_of_dvd_right h5b' a
      -- combine to get 10 ∣ a * b
      rcases h2ab with ⟨k, hk⟩
      rcases h5ab with ⟨l, hl⟩
      have h5k : (5 : ℕ) ∣ k := by
        have : (5 : ℕ) ∣ 2 * k := by
          simpa [hk] using hl
        have hcop : Nat.Coprime (5) (2) :=
          (Nat.coprime_comm).1 (Nat.coprime_two_left 5)
        exact (Nat.Coprime.dvd_of_dvd_mul_left hcop) this
      rcases h5k with ⟨m, hm⟩
      have h10ab : (10 : ℕ) ∣ a * b := by
        refine ⟨10 * m, ?_⟩
        calc
          a * b = 2 * k := hk
          _ = 2 * (5 * m) := by simpa [hm]
          _ = 10 * m := by ring
      have hpos : 0 < a * b := Nat.mul_pos ha hb
      exact Nat.le_of_dvd hpos h10ab
