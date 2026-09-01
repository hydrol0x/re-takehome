import Mathlib

abbrev m02_answer : ℕ :=
  Nat.find (by
    refine ⟨20, ?_, ?_⟩
    · norm_num
    · norm_num)

theorem m02_ord25 :
    IsLeast {n : ℕ | 0 < n ∧ 2 ^ n % 25 = 1} m02_answer := by
  have h_ex : ∃ n : ℕ, 0 < n ∧ 2 ^ n % 25 = 1 := by
    refine ⟨20, ?_, ?_⟩
    · norm_num
    · norm_num
  dsimp [m02_answer] at *
  have h_spec := Nat.find_spec h_ex
  have h_min := Nat.find_min' h_ex
  refine ⟨?mem, ?least⟩
  · simpa using h_spec
  · intro n hn
    exact h_min hn
