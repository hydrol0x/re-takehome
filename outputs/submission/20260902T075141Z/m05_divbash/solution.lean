import Mathlib

-- Basic arithmetic identities
lemma four_times_plus_two {n : ℕ} : 4 * (n + 2) = 4 * n + 8 := by
  linarith

lemma expand_square {n : ℕ} : (n + 2) ^ 2 = n ^ 2 + 4 * n + 4 := by
  linarith

-- Divisibility basics
lemma dvd_sub_of_dvd_both {a b c : ℕ} (h1 : a ∣ b) (h2 : a ∣ c) (hle : c ≤ b) : a ∣ b - c := by
  exact?

lemma dvd_of_dvd_and_le {a b : ℕ} (ha : 0 < a) (h : a ∣ b) : a ≤ b := by
  sorry

-- Forward direction helpers
lemma fwd_step1 {n : ℕ} (h : (n + 2) ∣ n ^ 2 + 4) : (n + 2) ∣ 4 * n := by
  have h1 : (n + 2) ∣ (n + 2) ^ 2 := by
    exact ⟨n + 2, by ring⟩
  have h2 : (n + 2) ∣ n ^ 2 + 4 := h
  have h3 : (n + 2) ^ 2 = n ^ 2 + 4 * n + 4 := by ring
  have h4 : 4 * n = (n + 2) ^ 2 - (n ^ 2 + 4) := by
    rw [show (n + 2) ^ 2 = n ^ 2 + 4 * n + 4 by ring]
    omega
  rw [h4]
  exact dvd_sub_of_dvd_both h1 h2 (by
    have : n ^ 2 + 4 ≤ (n + 2) ^ 2 := by
      rw [pow_two]
      ring_nf
      nlinarith
    exact this)

lemma fwd_step2 {n : ℕ} (h : (n + 2) ∣ 4 * n) : (n + 2) ∣ 8 := by
  have h1 : (n + 2) ∣ 4 * (n + 2) := by
    exact ⟨4, by ring⟩
  have h2 : 4 * n ≤ 4 * (n + 2) := by
    nlinarith
  have h3 : 4 * (n + 2) = 4 * n + 8 := by ring
  rw [show 8 = 4 * (n + 2) - 4 * n by rw [h3]; omega]
  exact dvd_sub_of_dvd_both h1 h (by omega)

lemma fwd_step3 {n : ℕ} (hn : 0 < n) (h : (n + 2) ∣ 8) : n ≤ 6 := by
  have h_bound : n + 2 ≤ 8 := Nat.le_of_dvd (by decide) h
  omega

-- Case checking for n ∈ {1,2,3,4,5,6}
lemma case_1_neg : ¬(1 + 2) ∣ 1 ^ 2 + 4 := by
  norm_num

lemma case_2_pos : (2 + 2) ∣ 2 ^ 2 + 4 := by
  norm_num

lemma case_3_neg : ¬(3 + 2) ∣ 3 ^ 2 + 4 := by
  norm_num

lemma case_4_neg : ¬(4 + 2) ∣ 4 ^ 2 + 4 := by
  norm_num

lemma case_5_neg : ¬(5 + 2) ∣ 5 ^ 2 + 4 := by
  norm_num

lemma case_6_pos : (6 + 2) ∣ 6 ^ 2 + 4 := by
  norm_num

theorem m05_divbash (n : ℕ) (hn : 0 < n) :
    (n + 2) ∣ n ^ 2 + 4 ↔ n = 2 ∨ n = 6 := by
  sorry
