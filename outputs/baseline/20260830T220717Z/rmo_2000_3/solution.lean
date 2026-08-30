import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.Linarith

open Finset

/-- Auxiliary lemma: for any natural `j ≥ 1`,
the sum of `1 / i` over `i ∈ Ico (j ^ 2) ((j + 1) ^ 2)` is at most `3 / j`. -/
lemma sum_one_div_Ico_sq_le (j : ℕ) (hj : 0 < j) :
    (Ico (j ^ 2) ((j + 1) ^ 2)).sum (fun i : ℕ => (1 : ℝ) / (i : ℝ))
      ≤ (3 : ℝ) / (j : ℝ) := by
  have hpos : ∀ i ∈ Ico (j ^ 2) ((j + 1) ^ 2), (0 : ℝ) ≤ (1 : ℝ) / (i : ℝ) := by
    intro i hi
    have : (0 : ℝ) < (i : ℝ) := by
      have : (j ^ 2) ≤ i := hi.1
      have : (0 : ℕ) ≤ i := Nat.zero_le _
      exact_mod_cast Nat.succ_le_of_lt (Nat.succ_lt_succ (Nat.succ_pos _))
    exact div_nonneg (by norm_num) (le_of_lt this)
  have hcard : ((Ico (j ^ 2) ((j + 1) ^ 2)).card : ℝ) = (2 * j + 1 : ℝ) := by
    have : ((Ico (j ^ 2) ((j + 1) ^ 2)).card) = (j + 1) ^ 2 - j ^ 2 := by
      simpa [Finset.card_Ico] using rfl
    simpa [Nat.pow_two, Nat.mul_add, Nat.add_mul, Nat.add_comm, Nat.add_left_comm,
      Nat.mul_comm, Nat.mul_left_comm, Nat.succ_eq_add_one, Nat.add_sub_cancel,
      Nat.sub_self, Nat.add_sub_cancel] using this
  have hle :
      (Ico (j ^ 2) ((j + 1) ^ 2)).sum (fun i : ℕ => (1 : ℝ) / (i : ℝ))
        ≤ ((Ico (j ^ 2) ((j + 1) ^ 2)).card : ℝ) * (1 / ((j ^ 2 : ℝ))) := by
    refine sum_le_card_nsmul ?_ ?_
    · intro i hi
      have hij : (j ^ 2 : ℝ) ≤ (i : ℝ) := by
        exact_mod_cast hi.1
      have : (1 : ℝ) / (i : ℝ) ≤ (1 : ℝ) / ((j ^ 2 : ℝ)) := by
        exact div_le_div_of_nonneg_left (by norm_num) (by exact_mod_cast hij)
      exact this
    · intro i hi
      exact hpos i hi
  have hcalc :
      ((Ico (j ^ 2) ((j + 1) ^ 2)).card : ℝ) * (1 / ((j ^ 2 : ℝ)))
        = (2 * (j : ℝ) + 1) / ((j : ℝ) * (j : ℝ)) := by
    have : ((j ^ 2 : ℝ)) = (j : ℝ) * (j : ℝ) := by
      norm_cast
    simpa [hcard, this, mul_comm, mul_left_comm, mul_assoc, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one, Nat.cast_bit0, Nat.cast_bit1] using rfl
  have hfinal : (2 * (j : ℝ) + 1) / ((j : ℝ) * (j : ℝ)) ≤ (3 : ℝ) / (j : ℝ) := by
    have hj' : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (Nat.lt_of_succ_lt (Nat.succ_lt_succ_iff.mp hj))
    have : (2 * (j : ℝ) + 1) ≤ 3 * (j : ℝ) := by
      have : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr (Nat.succ_le_of_lt (Nat.succ_pos _)))
      linarith
    have : (2 * (j : ℝ) + 1) / ((j : ℝ) * (j : ℝ)) ≤ (3 * (j : ℝ)) / ((j : ℝ) * (j : ℝ)) := by
      exact div_le_div_of_nonneg_right this (by positivity)
    simpa [mul_comm, mul_left_comm, mul_assoc, div_mul_eq_mul_div] using this
  have : (Ico (j ^ 2) ((j + 1) ^ 2)).sum (fun i : ℕ => (1 : ℝ) / (i : ℝ))
        ≤ (2 * (j : ℝ) + 1) / ((j : ℝ) * (j : ℝ)) := le_trans hle (by
          simpa [hcalc])
  exact le_trans this hfinal

/-- Main theorem. -/
theorem rmo_2000_3
  (x : ℕ → ℝ)
  (hpos : ∀ n, 0 < x n)
  (hmono : ∀ n, x n ≥ x (n + 1))
  (hsq : ∀ N, (Ico 1 (N + 1)).sum (fun i => x (i * i) / (i : ℝ)) ≤ 1) :
  ∀ k, (Ico 1 (k + 1)).sum (fun i => x i / (i : ℝ)) ≤ 3 := by
  intro k
  have hkpos : 0 < k + 1 := Nat.succ_pos _
  have hsubset :
      (Ico 1 (k + 1)).subset (Ico 1 ((k + 1) ^ 2)) := by
    intro i hi
    have : (i : ℕ) < k + 1 := hi.2
    have : (i : ℕ) ≤ (k + 1) ^ 2 - 1 := by
      have : (i : ℕ) ≤ k := Nat.le_of_lt_succ this
      have : (i : ℕ) ≤ (k + 1) ^ 2 - 1 := by
        have hpow : (k + 1) ≤ (k + 1) ^ 2 := by
          have : 1 ≤ (k + 1) := Nat.succ_le_succ (Nat.zero_le k)
          exact Nat.le_pow_self this (by decide)
        exact Nat.le_of_lt_succ (Nat.lt_of_le_of_lt this (Nat.sub_lt (Nat.succ_pos _) (Nat.succ_pos _)))
      exact this
    exact ⟨hi.1, Nat.lt_of_lt_of_le hi.2 (Nat.lt_succ_iff.mpr (Nat.le_of_lt_succ this))⟩
  have hnonneg : ∀ i ∈ Ico 1 ((k + 1) ^ 2), (0 : ℝ) ≤ x i / (i : ℝ) := by
    intro i hi
    have : (0 : ℝ) < x i := hpos i
    have : (0 : ℝ) ≤ (i : ℝ) := by exact_mod_cast Nat.zero_le i
    exact div_nonneg (le_of_lt this) (le_of_lt (by exact_mod_cast Nat.succ_pos i))
  have hle :
      (Ico 1 (k + 1)).sum (fun i => x i / (i : ℝ))
        ≤ (Ico 1 ((k + 1) ^ 2)).sum (fun i => x i / (i : ℝ)) := by
    exact sum_le_sum_of_subset hsubset (by
      intro i hi hnot
      exact hnonneg i hi)
  -- split the large sum into blocks
  have hblock :
      (Ico 1 ((k + 1) ^ 2)).sum (fun i => x i / (i : ℝ))
        ≤
        (∑ j in Ico 1 (k + 2), (x (j * j) / (j : ℝ)) * ((Ico (j ^ 2) ((j + 1) ^ 2)).sum (fun i => (1 : ℝ) / (i : ℝ)))) := by
    have hdisj : Pairwise (Disjoint on fun j : ℕ => Ico (j ^ 2) ((j + 1) ^ 2)) := by
      intro a ha b hb hne
      have hlt : a < b ∨ b < a := lt_or_gt_of_ne hne
      cases hlt with
      | inl hlt =>
        have : (Ico (a ^ 2) ((a + 1) ^ 2)).max' ? ≤ (b ^ 2) := by
          have : (a + 1) ^ 2 ≤ b ^ 2 := by
            have : a + 1 ≤ b := Nat.succ_le_of_lt hlt
            exact Nat.pow_le_pow_of_le_left (Nat.succ_le_iff.mpr this) 2
          exact this
        exact disjoint_left.2 (by
          intro x hx hx'
          have hxle : x < (a + 1) ^ 2 := hx.2
          have hxge : (b ^ 2) ≤ x := hx'.1
          have : (b ^ 2) ≤ (a + 1) ^ 2 - 1 := Nat.le_of_lt_succ hxle
          exact Nat.not_lt_of_ge (Nat.le_trans this hxge) hxle)
      | inr hgt =>
        have hsymm := (by
          have := hdisj b hb a ha (by simpa [ne_comm] using hne)
          exact this)
        exact hsymm
    have hcover : (Ico 1 ((k + 1) ^ 2)) ⊆
        (⋃ j ∈ Ico 1 (k + 2), Ico (j ^ 2) ((j + 1) ^ 2)) := by
      intro i hi
      have hi1 : (1 : ℕ) ≤ i := hi.1
      have hi2 : i < (k + 1) ^ 2 := hi.2
      let j := Nat.sqrt i
      have hjle : j ^ 2 ≤ i := Nat.sqrt_le_self _
      have hjsucc : i < (j + 1) ^ 2 := by
        have : i < (Nat.sqrt i + 1) ^ 2 := Nat.lt_succ_self _
        simpa [j] using this
      have hjpos : 0 < j + 1 := Nat.succ_pos _
      have : j + 1 ≤ k + 1 := by
        have : i < (k + 1) ^ 2 := hi2
        have : (j + 1) ^ 2 ≤ (k + 1) ^ 2 := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hjsucc (Nat.le_of_lt_succ hi2))
        exact Nat.le_of_pow_le_pow this (by decide)
      have hmemj : j + 1 ∈ Ico 1 (k + 2) := by
        have : (1 : ℕ) ≤ j + 1 := Nat.succ_le_succ (Nat.zero_le _)
        have : j + 1 < k + 2 := Nat.succ_lt_succ this
        exact ⟨this, this⟩
      have : i ∈ Ico (j ^ 2) ((j + 1) ^ 2) := ⟨hjle, hjsucc⟩
      exact mem_iUnion.2 ⟨j + 1, mem_iUnion.2 ⟨hmemj, this⟩⟩
    have hsum :
        (Ico 1 ((k + 1) ^ 2)).sum (fun i => x i / (i : ℝ))
          = ∑ j in Ico 1 (k + 2),
              ∑ i in Ico (j ^ 2) ((j + 1) ^ 2), x i / (i : ℝ) := by
      refine (Finset.sum_bij' (fun i hi => ?_) ?_ ?_ ?_ ?_).symm
      ·
        let j := Nat.findGreatest (fun j => j ^ 2 ≤ i) i
        have hj : j ^ 2 ≤ i ∧ i < (j + 1) ^ 2 := Nat.findGreatest_spec (fun j => j ^ 2 ≤ i) i (by
          have : (0 : ℕ) ^ 2 ≤ i := Nat.zero_le _
          exact this)
        exact ⟨j, ?_, ?_⟩
      sorry
    sorry
  have hfinal :
      (Ico 1 (k + 1)).sum (fun i => x i / (i : ℝ)) ≤ 3 := by
    have hbound :
        (∑ j in Ico 1 (k + 2), (x (j * j) / (j : ℝ)) *
            ((Ico (j ^ 2) ((j + 1) ^ 2)).sum (fun i => (1 : ℝ) / (i : ℝ)))) ≤ 3 := by
      have hsum :
          (∑ j in Ico 1 (k + 2), (x (j * j) / (j : ℝ)) *
              ((Ico (j ^ 2) ((j + 1) ^ 2)).sum (fun i => (1 : ℝ) / (i : ℝ))))
            ≤ ∑ j in Ico 1 (k + 2), (x (j * j) / (j : ℝ)) * (3 / (j : ℝ)) := by
        refine sum_le_sum ?_
        intro j hj
        have : (0 : ℝ) ≤ x (j * j) / (j : ℝ) := by
          have : (0 : ℝ) < x (j * j) := hpos (j * j)
          have : (0 : ℝ) ≤ (j : ℝ) := by exact_mod_cast Nat.zero_le j
          exact div_nonneg (le_of_lt this) (by exact_mod_cast Nat.zero_le j)
        have hle := mul_le_mul_of_nonneg_left (sum_one_div_Ico_sq_le j (by
          have : (0 : ℕ) < j := Nat.succ_le_iff.mp hj.1
          exact this)) this
        simpa [mul_comm, mul_left_comm, mul_assoc] using hle
      have hsum2 :
          (∑ j in Ico 1 (k + 2), (x (j * j) / (j : ℝ)) * (3 / (j : ℝ)))
            = 3 * (∑ j in Ico 1 (k + 2), x (j * j) / (j : ℝ)) := by
        have : (∑ j in Ico 1 (k + 2), (x (j * j) / (j : ℝ)) * (3 / (j : ℝ)))
            = ∑ j in Ico 1 (k + 2), (3 : ℝ) * (x (j * j) / (j : ℝ) / (j : ℝ)) := by
          apply sum_congr rfl
          intro j hj
          ring
        simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv, mul_inv_cancel_left₀] using this
      have hle2 : (∑ j in Ico 1 (k + 2), x (j * j) / (j : ℝ)) ≤ 1 := by
        have := hsq (k + 1)
        simpa [Nat.add_comm, Nat.succ_eq_add_one] using this
      have : (∑ j in Ico 1 (k + 2), (x (j * j) / (j : ℝ)) *
            ((Ico (j ^ 2) ((j + 1) ^ 2)).sum (fun i => (1 : ℝ) / (i : ℝ)))) ≤ 3 := by
        calc
          _ ≤ ∑ j in Ico 1 (k + 2), (x (j * j) / (j : ℝ)) * (3 / (j : ℝ)) := hsum
          _ = 3 * (∑ j in Ico 1 (k + 2), x (j * j) / (j : ℝ)) := by
            simpa [mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using hsum2
          _ ≤ 3 * (1 : ℝ) := by
            gcongr
            exact hle2
          _ = 3 := by norm_num
        exact this
      exact this
    exact le_trans hle hfinal
  exact hfinal
