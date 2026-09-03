-- Reference proof for the REVISED rmo_2000_6 (upstream PR #9: both bounds 10).
--
-- Import-surface constraint (established 2026-09-01, probes in EXPERIMENTS.md):
-- the Comparator compares kernel-level statements, and this challenge's
-- statement elaborates differently under `import Mathlib.Tactic` or
-- `import Mathlib` than under the challenge's own two imports — so any
-- solution using those imports fails with "statement do not match" even
-- when its proof is mathematically correct (as happened to the duo's
-- REPL-accepted proof in run 20260831T191439Z). This proof therefore uses
-- ONLY the challenge's import surface plus Lean-core tactics
-- (omega / decide / obtain / rcases / subst), with 100-case bounded
-- exhaustion via `decide` in place of Mathlib's interval_cases/norm_num.
-- Comparator-validated: passed=True, ~14 s (see EXPERIMENTS.md).
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Bounds.Basic

theorem rmo_2000_6 :
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 2 * b ^ 5 ∧ n = a * b} 10) ∧
  (IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ 2000 ∣ a ^ 3 * b ^ 4 ∧ n = a * b} 10) := by
  constructor
  · constructor
    · exact ⟨1, 10, by omega, by omega, ⟨50, by decide⟩, by decide⟩
    · intro n hn
      obtain ⟨a, b, ha, hb, hdvd, heq⟩ := hn
      subst heq
      have hab1 : a ≤ a * b := Nat.le_mul_of_pos_right a hb
      have hab2 : b ≤ a * b := Nat.le_mul_of_pos_left b ha
      rcases Nat.lt_or_ge (a * b) 10 with hlt | hge
      · exfalso
        obtain ⟨c, hc⟩ := hdvd
        have hmod : (a ^ 2 * b ^ 5) % 2000 = 0 := by omega
        have key : ∀ a' < 10, ∀ b' < 10, 0 < a' → 0 < b' → a' * b' < 10 → (a' ^ 2 * b' ^ 5) % 2000 ≠ 0 := by decide
        exact key a (by omega) b (by omega) ha hb hlt hmod
      · exact hge
  · constructor
    · exact ⟨5, 2, by omega, by omega, ⟨1, by decide⟩, by decide⟩
    · intro n hn
      obtain ⟨a, b, ha, hb, hdvd, heq⟩ := hn
      subst heq
      have hab1 : a ≤ a * b := Nat.le_mul_of_pos_right a hb
      have hab2 : b ≤ a * b := Nat.le_mul_of_pos_left b ha
      rcases Nat.lt_or_ge (a * b) 10 with hlt | hge
      · exfalso
        obtain ⟨c, hc⟩ := hdvd
        have hmod : (a ^ 3 * b ^ 4) % 2000 = 0 := by omega
        have key : ∀ a' < 10, ∀ b' < 10, 0 < a' → 0 < b' → a' * b' < 10 → (a' ^ 3 * b' ^ 4) % 2000 ≠ 0 := by decide
        exact key a (by omega) b (by omega) ha hb hlt hmod
      · exact hge
