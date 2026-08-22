import Mathlib

open Finset

theorem rmo_2000_3
  (x : ℕ → ℝ)
  (hpos : ∀ n, 0 < x n)
  (hmono : ∀ n, x n ≥ x (n + 1))
  (hsq : ∀ N, (Ico 1 (N + 1)).sum (fun i => x (i * i) / (i : ℝ)) ≤ 1) :
  ∀ k, (Ico 1 (k + 1)).sum (fun i => x i / (i : ℝ)) ≤ 3 := by
  have hanti : Antitone x := antitone_nat_of_succ_le fun n => hmono n
  -- Block bound: for 1 ≤ j, the sum over [j*j, (j+1)*(j+1)) is at most 3·x(j²)/j.
  have hblock : ∀ j : ℕ, 1 ≤ j →
      (Ico (j * j) ((j + 1) * (j + 1))).sum (fun i => x i / (i : ℝ))
        ≤ 3 * (x (j * j) / (j : ℝ)) := by
    intro j hj
    have hc1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hc0 : (0 : ℝ) < (j : ℝ) := by linarith
    have hX : (0 : ℝ) < x (j * j) := hpos _
    have hjj : (0 : ℝ) < (j : ℝ) * (j : ℝ) := mul_pos hc0 hc0
    have hterm : ∀ i ∈ Ico (j * j) ((j + 1) * (j + 1)),
        x i / (i : ℝ) ≤ x (j * j) / ((j : ℝ) * (j : ℝ)) := by
      intro i hi
      obtain ⟨hi1, _hi2⟩ := Finset.mem_Ico.mp hi
      have hxle : x i ≤ x (j * j) := hanti hi1
      have hile : (j : ℝ) * (j : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi1
      gcongr <;> first
        | exact hxle
        | exact hile
        | positivity
        | linarith [hX, hjj]
    have hsum := Finset.sum_le_card_nsmul _ _ _ hterm
    rw [Nat.card_Ico] at hsum
    have hcard : (j + 1) * (j + 1) - j * j = 2 * j + 1 := by
      have h : (j + 1) * (j + 1) = j * j + (2 * j + 1) := by ring
      omega
    rw [hcard, nsmul_eq_mul] at hsum
    refine le_trans hsum ?_
    have hcast : ((2 * j + 1 : ℕ) : ℝ) = 2 * (j : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    have hu : (0 : ℝ) ≤ x (j * j) / ((j : ℝ) * (j : ℝ)) := le_of_lt (div_pos hX hjj)
    have hwc : x (j * j) / (j : ℝ) = x (j * j) / ((j : ℝ) * (j : ℝ)) * (j : ℝ) := by
      field_simp
    rw [hwc]
    nlinarith [hu, hc1]
  -- Prefix sums up to block boundaries, by induction on the number of blocks.
  have hmain : ∀ J : ℕ, (Ico 1 ((J + 1) * (J + 1))).sum (fun i => x i / (i : ℝ))
      ≤ 3 * (Ico 1 (J + 1)).sum (fun j => x (j * j) / (j : ℝ)) := by
    intro J
    induction J with
    | zero => simp
    | succ J ih =>
        have hb1 : 1 ≤ (J + 1) * (J + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
        have hb2 : (J + 1) * (J + 1) ≤ (J + 2) * (J + 2) := by nlinarith
        have hsplit := Finset.sum_Ico_consecutive
          (fun i => x i / (i : ℝ)) hb1 hb2
        have hstep := hblock (J + 1) (Nat.succ_le_succ (Nat.zero_le J))
        have htop : (Ico 1 (J + 1 + 1)).sum (fun j => x (j * j) / (j : ℝ))
            = (Ico 1 (J + 1)).sum (fun j => x (j * j) / (j : ℝ))
              + x ((J + 1) * (J + 1)) / ((J + 1 : ℕ) : ℝ) :=
          Finset.sum_Ico_succ_top (Nat.succ_le_succ (Nat.zero_le J)) _
        have hgoal : (J + 1 + 1) * (J + 1 + 1) = (J + 2) * (J + 2) := by ring
        rw [hgoal] at hstep
        rw [hgoal, ← hsplit, htop]
        push_cast at hstep htop ih ⊢
        linarith [ih, hstep]
  intro k
  have hk1 : k + 1 ≤ (k + 1) * (k + 1) := Nat.le_mul_of_pos_left (k + 1) (by omega)
  have hext : (Ico 1 (k + 1)).sum (fun i => x i / (i : ℝ))
      ≤ (Ico 1 ((k + 1) * (k + 1))).sum (fun i => x i / (i : ℝ)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico le_rfl hk1)
    intro i _ _
    exact div_nonneg (hpos i).le (Nat.cast_nonneg i)
  have h3 := hmain k
  have h4 := hsq k
  linarith [hext, h3, h4]
