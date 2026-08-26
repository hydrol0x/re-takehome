import Mathlib

lemma two_pow_mod_7_cases (n : ℕ) : 2 ^ n % 7 = 
  if n % 3 = 0 then 1 else 
  if n % 3 = 1 then 2 else 4 := by induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
    rcases this with (h | h | h) <;>
      simp_all [Nat.mul_mod, Nat.pow_mod, Nat.add_mod] <;>
      try omega

lemma three_dvd_iff_mod_zero (n : ℕ) : 3 ∣ n ↔ n % 3 = 0 := by omega

lemma div_sub_one_iff_mod_eq (n : ℕ) (h : 1 ≤ 2 ^ n) : 
  7 ∣ 2 ^ n - 1 ↔ 2 ^ n % 7 = 1 := by omega

lemma two_pow_plus_one_mod_ne_zero (n : ℕ) : (2 ^ n + 1) % 7 ≠ 0 := by
  have h₁ : 2 ^ n % 7 = if n % 3 = 0 then 1 else if n % 3 = 1 then 2 else 4 := two_pow_mod_7_cases n
  by_cases h₂ : n % 3 = 0 <;>
    by_cases h₃ : n % 3 = 1 <;>
      simp_all [Nat.add_mod] <;>
      omega

lemma two_pow_ge_one_for_pos (n : ℕ) (hn : 0 < n) : 1 ≤ 2 ^ n := by
  exact Nat.succ_le_of_lt (by positivity)

theorem p09_a (n : ℕ) (hn : 0 < n) : 7 ∣ 2 ^ n - 1 ↔ 3 ∣ n := by
  have h_bound : 1 ≤ 2 ^ n := two_pow_ge_one_for_pos n hn
  rw [div_sub_one_iff_mod_eq n h_bound]
  rw [two_pow_mod_7_cases n]
  rw [three_dvd_iff_mod_zero]
  by_cases h : n % 3 = 0 <;>
    by_cases h' : n % 3 = 1 <;>
      simp_all <;>
      omega

theorem p09_b (n : ℕ) (hn : 0 < n) : ¬7 ∣ 2 ^ n + 1 := by
  intro h
  have h_mod_ne : (2 ^ n + 1) % 7 ≠ 0 := two_pow_plus_one_mod_ne_zero n
  have h_mod_eq : (2 ^ n + 1) % 7 = 0 := Nat.mod_eq_zero_of_dvd h
  exact h_mod_ne h_mod_eq
