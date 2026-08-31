import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open Finset

theorem rmo_2000_3
  (x : ℕ → ℝ)
  (hpos : ∀ n, 0 < x n)
  (hmono : ∀ n, x n ≥ x (n + 1))
  (hsq : ∀ N, (Ico 1 (N + 1)).sum (fun i => x (i * i) / (i : ℝ)) ≤ 1) :
  ∀ k, (Ico 1 (k + 1)).sum (fun i => x i / (i : ℝ)) ≤ 3 := by
  intro k
  -- Let m = ⌊√k⌋.
  set m : ℕ := Nat.sqrt k with hm
  have hk : k < (m + 1) * (m + 1) := by
    have : m * m ≤ k := Nat.sqrt_mul_self_le k
    have : k < (Nat.sqrt k + 1) ^ 2 := Nat.lt_succ_self_mul_self_succ k
    simpa [hm, Nat.pow_two] using this
  -- Split the sum at m.
  have hsplit :
      (Ico 1 (k + 1)).sum (fun i => x i / (i : ℝ)) =
        (Ico 1 (m + 1)).sum (fun i => x i / (i : ℝ)) +
        (Ico (m + 1) (k + 1)).sum (fun i => x i / (i : ℝ)) := by
    have : (Ico 1 (k + 1)) = (Ico 1 (m + 1)) ∪ (Ico (m + 1) (k + 1)) := by
      ext i; constructor
      · intro hi
        rcases mem_Ico.1 hi with ⟨h1, h2⟩
        have hle : i ≤ m ∨ m + 1 ≤ i := le_or_lt i (m + 1) |> Or.imp_left (fun h => le_of_lt h) (fun h => le_of_lt h)
        cases hle with
        | inl hle =>
          have : i ∈ Ico 1 (m + 1) := by
            have : 1 ≤ i := h1
            have : i < m + 1 := Nat.lt_of_le_of_ne hle (Nat.ne_of_lt (Nat.lt_succ_self _))
            exact mem_Ico.2 ⟨this, this⟩
          exact Or.inl this
        | inr hge =>
          have : i ∈ Ico (m + 1) (k + 1) := by
            have : m + 1 ≤ i := hge
            have : i < k + 1 := h2
            exact mem_Ico.2 ⟨this, this⟩
          exact Or.inr this
      · intro h
        rcases h with h | h
        · exact (mem_Ico.1 h).1.trans (Nat.succ_le_of_lt (Nat.lt_succ_self _))
        · exact (mem_Ico.1 h).2
    have hdisj : Disjoint (Ico 1 (m + 1)) (Ico (m + 1) (k + 1)) := by
      apply disjoint_left.2
      intro a ha hb
      rcases mem_Ico.1 ha with ⟨h1a, h2a⟩
      rcases mem_Ico.1 hb with ⟨h1b, h2b⟩
      exact Nat.not_lt_of_ge h2a h1b
    simpa [sum_union hdisj] using congrArg (fun s => s.sum (fun i => x i / (i : ℝ))) this
  have hfirst : (Ico 1 (m + 1)).sum (fun i => x i / (i : ℝ)) ≤ 1 := by
    have := hsq (m + 1)
    simpa [Nat.succ_eq_add_one, Nat.mul_comm] using this
  have hsecond : (Ico (m + 1) (k + 1)).sum (fun i => x i / (i : ℝ)) ≤ 2 := by
    have hcard : (Ico (m + 1) (k + 1)).card ≤ m * (m + 1) := by
      have : k < (m + 1) * (m + 1) := hk
      have hk' : k + 1 ≤ (m + 1) * (m + 1) := Nat.succ_le_of_lt this
      have : (Ico (m + 1) (k + 1)).card = k + 1 - (m + 1) := by
        simpa [card_Ico] using rfl
      have : k + 1 - (m + 1) ≤ (m + 1) * (m + 1) - (m + 1) := Nat.sub_le_sub_right hk' _
      simpa [Nat.mul_sub_left_distrib, Nat.one_mul, Nat.succ_mul, Nat.mul_succ, Nat.add_comm,
        Nat.add_left_comm, Nat.add_assoc] using this
    have hbound : ∀ i ∈ Ico (m + 1) (k + 1), x i / (i : ℝ) ≤ x (m + 1) / (m + 1 : ℝ) := by
      intro i hi
      have hle : m + 1 ≤ i := (mem_Ico.1 hi).1
      have hmono' : x i ≤ x (m + 1) := by
        have : i ≥ m + 1 := hle
        exact le_of_lt (lt_of_lt_of_le (hpos (m + 1)) (hmono (m + 1)))
      have hposi : (0 : ℝ) < (i : ℝ) := by exact_mod_cast Nat.cast_pos.mpr (Nat.succ_le_iff.mp hle)
      have hposm : (0 : ℝ) < (m + 1 : ℝ) := by exact_mod_cast Nat.succ_pos _
      have : x i / (i : ℝ) ≤ x (m + 1) / (m + 1 : ℝ) := by
        have := div_le_div_of_le hmono' (by exact_mod_cast Nat.le_of_lt hposi) hposi hposm
        simpa using this
      exact this
    have : (Ico (m + 1) (k + 1)).sum (fun i => x i / (i : ℝ)) ≤
        (Ico (m + 1) (k + 1)).card • (x (m + 1) / (m + 1 : ℝ)) := by
      apply sum_le_sum
      intro i hi
      exact hbound i hi
    have : (Ico (m + 1) (k + 1)).sum (fun i => x i / (i : ℝ)) ≤
        (m * (m + 1) : ℝ) * (x (m + 1) / (m + 1 : ℝ)) := by
      have := this
      have hcard' : (Ico (m + 1) (k + 1)).card ≤ m * (m + 1) := hcard
      have hcard'' : ((Ico (m + 1) (k + 1)).card : ℝ) ≤ (m * (m + 1) : ℝ) :=
        by exact_mod_cast hcard'
      have : ((Ico (m + 1) (k + 1)).card : ℝ) • (x (m + 1) / (m + 1 : ℝ)) ≤
          (m * (m + 1) : ℝ) • (x (m + 1) / (m + 1 : ℝ)) :=
        smul_le_smul_of_nonneg (by exact_mod_cast hcard'') (by norm_num)
      exact le_trans this (by simpa using this)
    have hx : x (m + 1) ≤ (m + 1 : ℝ) := by
      have := hsq (m + 1)
      have hterm : x ((m + 1) * (m + 1)) / (m + 1 : ℝ) ≤ (Ico 1 ((m + 1) + 1)).sum (fun i => x (i * i) / (i : ℝ)) :=
        by
          apply le_of_lt
          have : (0 : ℝ) < 1 := by norm_num
          exact this
      have : x ((m + 1) * (m + 1)) ≤ (m + 1 : ℝ) := by
        have := le_of_lt (by
          have : (x ((m + 1) * (m + 1)) / (m + 1 : ℝ)) ≤ 1 := le_trans hterm (hsq (m + 1))
          have hpos : (0 : ℝ) < (m + 1 : ℝ) := by exact_mod_cast Nat.succ_pos _
          have := (div_le_iff hpos).mp this
          simpa [mul_comm] using this)
        exact this
      have hmono' : x (m + 1) ≤ x ((m + 1) * (m + 1)) := by
        have : (m + 1) ≤ (m + 1) * (m + 1) := Nat.le_mul_of_pos_right (Nat.succ_pos _)
        exact hmono (Nat.le_of_lt_succ this)
      exact le_trans hmono' this
    have : (Ico (m + 1) (k + 1)).sum (fun i => x i / (i : ℝ)) ≤ 2 := by
      have : (m * (m + 1) : ℝ) * (x (m + 1) / (m + 1 : ℝ)) ≤ 2 := by
        have : (m : ℝ) ≤ 2 / (x (m + 1) / (m + 1 : ℝ)) := by
          have : (x (m + 1) / (m + 1 : ℝ)) ≤ 1 := by
            have : x (m + 1) ≤ (m + 1 : ℝ) := hx
            have : (x (m + 1) / (m + 1 : ℝ)) ≤ ((m + 1 : ℝ) / (m + 1 : ℝ)) := by
              exact div_le_div_of_le (by exact hx) (by exact_mod_cast Nat.succ_pos _) (by exact_mod_cast Nat.succ_pos _)
            simpa using this
          have : (m : ℝ) * (x (m + 1) / (m + 1 : ℝ)) ≤ (m : ℝ) * 1 := by
            exact mul_le_mul_of_nonneg_left this (by exact_mod_cast Nat.zero_le _)
          have : (m : ℝ) * (x (m + 1) / (m + 1 : ℝ)) ≤ (m : ℝ) := by simpa using this
          have : (m : ℝ) ≤ 2 := by
            have : (m : ℝ) ≤ (m + 1 : ℝ) := by exact_mod_cast Nat.le_succ _
            have : (m + 1 : ℝ) ≤ 2 := by
              have : m ≤ 1 := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_of_lt_succ hk))
              exact_mod_cast this
            exact le_trans this this
          exact le_of_lt (by norm_num)
        have : (m * (m + 1) : ℝ) * (x (m + 1) / (m + 1 : ℝ)) ≤ 2 := by
          have : (m : ℝ) * (x (m + 1) / (m + 1 : ℝ)) ≤ 1 := by
            have : (x (m + 1) / (m + 1 : ℝ)) ≤ 1 := by
              have : x (m + 1) ≤ (m + 1 : ℝ) := hx
              have : (x (m + 1) / (m + 1 : ℝ)) ≤ ((m + 1 : ℝ) / (m + 1 : ℝ)) := by
                exact div_le_div_of_le (by exact hx) (by exact_mod_cast Nat.succ_pos _) (by exact_mod_cast Nat.succ_pos _)
              simpa using this
            have : (m : ℝ) ≤ 1 := by
              have : m ≤ 1 := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_of_lt_succ hk))
              exact_mod_cast this
            exact mul_le_mul_of_nonneg_left this (by norm_num)
          have : (m * (m + 1) : ℝ) * (x (m + 1) / (m + 1 : ℝ)) = (m : ℝ) * ((m + 1 : ℝ) * (x (m + 1) / (m + 1 : ℝ))) := by
            ring
          simpa [this] using mul_le_mul_of_nonneg_left this (by norm_num)
        exact this
      exact le_trans this (by norm_num)
    exact this
  have : (Ico 1 (k + 1)).sum (fun i => x i / (i : ℝ)) ≤ 1 + 2 := by
    simpa [hsplit] using add_le_add hfirst hsecond
  simpa [one_add_one_eq_two, add_comm] using this
