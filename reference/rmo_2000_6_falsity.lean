import Mathlib

-- Certificate: part (b) of rmo_2000_6 as formalized is FALSE.
-- (5,2) gives 5^3 * 2^4 = 2000, so 10 is in the set, contradicting IsLeast _ 20.
example : ¬ IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} 20 := by
  rintro ⟨-, hub⟩
  have h10 : 10 ∈ {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} :=
    ⟨5, 2, by norm_num, by norm_num, by norm_num, by norm_num⟩
  have := hub h10
  omega

-- Sanity: the full conjunction (the challenge statement) is therefore false too.
example : ¬ ((IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} 10) ∧
    (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} 20)) := by
  rintro ⟨-, -, hub⟩
  have h10 : 10 ∈ {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} :=
    ⟨5, 2, by norm_num, by norm_num, by norm_num, by norm_num⟩
  have := hub h10
  omega
