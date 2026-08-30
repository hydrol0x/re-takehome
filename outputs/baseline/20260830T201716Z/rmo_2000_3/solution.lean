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
  classical
  -- Handle the case k = 0 separately
  by_cases hk : k = 0
  · rw [hk]
    simp [Ico]
    <;> norm_num
  -- For k > 0, use the decomposition into square blocks
  have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
  let m := Nat.sqrt k
  have h_m_sq_le_k : m * m ≤ k := Nat.sqrt_le' k
  have h_k_lt_m_add_1_sq : k < (m + 1) * (m + 1) := Nat.lt_succ_sqrt_mul_self k
  
  -- Key lemma: for each j ≥ 1, the sum over [j², (j+1)²) is bounded
  have h_block_bound : ∀ j : ℕ, 1 ≤ j → 
    ∑ i ∈ Ico (j * j) ((j + 1) * (j + 1)), x i / (i : ℝ) ≤ x (j * j) * ∑ i ∈ Ico (j * j) ((j + 1) * (j + 1)), (1 : ℝ) / (i : ℝ) := by
    intro j hj
    have h_mono_j : ∀ i ∈ Ico (j * j) ((j + 1) * (j + 1)), x i ≤ x (j * j) := by
      intro i hi
      have h_ge : j * j ≤ i := hi.1
      have h_lt : i < (j + 1) * (j + 1) := hi.2
      exact hmono _ |>.trans (by linarith)
    calc
      ∑ i ∈ Ico (j * j) ((j + 1) * (j + 1)), x i / (i : ℝ) ≤ 
        ∑ i ∈ Ico (j * j) ((j + 1) * (j + 1)), x (j * j) / (i : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        have h₁ : 0 < (i : ℝ) := by
          have h₂ : j * j ≤ i := hi.1
          have h₃ : 0 < j := by linarith
          have h₄ : 0 < j * j := by positivity
          linarith
        have h₂ : x i ≤ x (j * j) := h_mono_j i hi
        have h₃ : 0 < x (j * j) := hpos (j * j)
        have h₄ : 0 < x i := hpos i
        field_simp [h₁.ne']
        rw [div_le_div_iff (by positivity) (by positivity)]
        nlinarith
      _ = x (j * j) * ∑ i ∈ Ico (j * j) ((j + 1) * (j + 1)), (1 : ℝ) / (i : ℝ) := by
        simp [Finset.mul_sum]
  
  -- Bound the harmonic sum over each block
  have h_harmonic_bound : ∀ j : ℕ, 1 ≤ j → 
    ∑ i ∈ Ico (j * j) ((j + 1) * (j + 1)), (1 : ℝ) / (i : ℝ) ≤ 2 / (j : ℝ) := by
    intro j hj
    have h₁ : ∑ i ∈ Ico (j * j) ((j + 1) * (j + 1)), (1 : ℝ) / (i : ℝ) ≤ 
      ∑ i ∈ Ico (j * j) ((j + 1) * (j + 1)), (1 : ℝ) / (j * j : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      have h₂ : j * j ≤ i := hi.1
      have h₃ : 0 < (j : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (by linarith))
      have h₄ : (i : ℝ) ≥ (j * j : ℝ) := by exact_mod_cast h₂
      have h₅ : (1 : ℝ) / (i : ℝ) ≤ (1 : ℝ) / (j * j : ℝ) := by
        apply one_div_le_one_div_of_le
        · positivity
        · exact_mod_cast h₂
      exact h₅
    have h₂ : ∑ i ∈ Ico (j * j) ((j + 1) * (j + 1)), (1 : ℝ) / (j * j : ℝ) = 
      ((j + 1) * (j + 1) - j * j : ℝ) / (j * j : ℝ) := by
      have h₃ : ∑ i ∈ Ico (j * j) ((j + 1) * (j + 1)), (1 : ℝ) / (j * j : ℝ) = 
        (Finset.card (Ico (j * j) ((j + 1) * (j + 1))) : ℝ) * ((1 : ℝ) / (j * j : ℝ)) := by
        simp [Finset.sum_const]
      rw [h₃]
      have h₄ : Finset.card (Ico (j * j) ((j + 1) * (j + 1))) = (j + 1) * (j + 1) - j * j := by
        simp [Ico, Finset.Ico_eq_empty_iff]
        <;> ring_nf
        <;> omega
      rw [h₄]
      <;> field_simp
      <;> ring_nf
    rw [h₂]
    have h₃ : ((j + 1) * (j + 1) - j * j : ℝ) / (j * j : ℝ) ≤ 2 / (j : ℝ) := by
      have h₄ : (j : ℝ) ≥ 1 := by exact_mod_cast (by linarith)
      have h₅ : (j : ℝ) > 0 := by linarith
      field_simp [h₅.ne']
      rw [div_le_div_iff (by positivity) (by positivity)]
      ring_nf
      nlinarith
    exact h₃
  
  -- Decompose the total sum into blocks
  have h_decomp : (Ico 1 (k + 1)).sum (fun i => x i / (i : ℝ)) = 
    ∑ j ∈ Ico 1 (m + 1), ∑ i ∈ Ico (j * j) ((j + 1) * (j + 1)) ∩ Ico 1 (k + 1), x i / (i : ℝ) := by
    have h₁ : (Ico 1 (k + 1)) = ⋃ j ∈ Ico 1 (m + 1), Ico (j * j) ((j + 1) * (j + 1)) ∩ Ico 1 (k + 1) := by
      ext i
      constructor
      · intro h
        have h₂ : 1 ≤ i ∧ i ≤ k := by simpa using h
        have h₃ : ∃ j, j ∈ Ico 1 (m + 1) ∧ j * j ≤ i ∧ i < (j + 1) * (j + 1) := by
          use Nat.sqrt i
          constructor
          · have h₄ : Nat.sqrt i < m + 1 := by
              have h₅ : i ≤ k := h₂.2
              have h₆ : Nat.sqrt i ≤ Nat.sqrt k := Nat.sqrt_le_sqrt h₅
              have h₇ : Nat.sqrt k = m := by rfl
              linarith
            have h₈ : Nat.sqrt i ≥ 1 := by
              have h₉ : 1 ≤ i := h₂.1
              have h₁₀ : 1 ≤ Nat.sqrt i := by
                apply Nat.le_sqrt.mpr
                norm_num
                linarith
              exact h₁₀
            exact ⟨h₈, h₄⟩
          · have h₄ : Nat.sqrt i * Nat.sqrt i ≤ i := Nat.sqrt_le' i
            have h₅ : i < (Nat.sqrt i + 1) * (Nat.sqrt i + 1) := Nat.lt_succ_sqrt_mul_self i
            exact ⟨h₄, h₅⟩
        rcases h₃ with ⟨j, hj, hji, hij⟩
        refine' ⟨j, hj, _⟩
        constructor
        · exact ⟨hji, h₂.1.le⟩
        · exact ⟨hij, h₂.2.le⟩
      · intro h
        rcases h with ⟨j, hj, hji, hij⟩
        have h₂ : 1 ≤ i := by
          have h₃ : j * j ≤ i := hji.1
          have h₄ : 1 ≤ j := hj.1
          nlinarith
        have h₃ : i ≤ k := by
          have h₄ : i < (j + 1) * (j + 1) := hji.2
          have h₅ : j ≤ m := hj.2
          have h₆ : (j + 1) * (j + 1) ≤ (m + 1) * (m + 1) := by
            gcongr
          have h₇ : k < (m + 1) * (m + 1) := h_k_lt_m_add_1_sq
          have h₈ : i < (m + 1) * (m + 1) := by linarith
          have h₉ : i ≤ k := by
            by_contra h₉
            have h₁₀ : k < i := by linarith
            have h₁₁ : i < (m + 1) * (m + 1) := by linarith
            have h₁₂ : k < (m + 1) * (m + 1) := h_k_lt_m_add_1_sq
            have h₁₃ : m * m ≤ k := h_m_sq_le_k
            have h₁₄ : i ≥ (m + 1) * (m + 1) := by
              have h₁₅ : ∃ j', j' ∈ Ico 1 (m + 1) ∧ j' * j' ≤ i ∧ i < (j' + 1) * (j' + 1) := by
                use Nat.sqrt i
                constructor
                · have h₁₆ : Nat.sqrt i < m + 1 := by
                    have h₁₇ : i ≤ k := by linarith
                    have h₁₈ : Nat.sqrt i ≤ Nat.sqrt k := Nat.sqrt_le_sqrt h₁₇
                    have h₁₉ : Nat.sqrt k = m := by rfl
                    linarith
                  have h₂₀ : Nat.sqrt i ≥ 1 := by
                    have h₂₁ : 1 ≤ i := by linarith
                    have h₂₂ : 1 ≤ Nat.sqrt i := by
                      apply Nat.le_sqrt.mpr
                      norm_num
                      linarith
                    exact h₂₂
                  exact ⟨h₂₀, h₁₆⟩
                · have h₂₃ : Nat.sqrt i * Nat.sqrt i ≤ i := Nat.sqrt_le' i
                  have h₂₄ : i < (Nat.sqrt i + 1) * (Nat.sqrt i + 1) := Nat.lt_succ_sqrt_mul_self i
                  exact ⟨h₂₃, h₂₄⟩
              rcases h₁₅ with ⟨j', hj', hji', hij'⟩
              have h₂₅ : j' ≤ m := hj'.2
              have h₂₆ : i < (j' + 1) * (j' + 1) := hij'.2
              have h₂₇ : (j' + 1) * (j' + 1) ≤ (m + 1) * (m + 1) := by
                gcongr
              linarith
            linarith
          exact h₉
        exact ⟨h₂, h₃⟩
    rw [h₁]
    rw [Finset.sum_Union]
    · intro j hj
      intro j' hj' h_int
      have h₂ : j ≠ j' := by
        intro h_eq
        rw [h_eq] at h_int
        simp at h_int
      have h₃ : Disjoint (Ico (j * j) ((j + 1) * (j + 1)) ∩ Ico 1 (k + 1)) 
                 (Ico (j' * j') ((j' + 1) * (j' + 1)) ∩ Ico 1 (k + 1)) := by
        apply Finset.disjoint_left.mpr
        intro i hi
        simp only [Finset.mem_inter, Finset.mem_Ico] at hi ⊢
        cases hi with
        | intro hi₁ hi₂ =>
          cases hi₁ with
          | intro hi₁a hi₁b =>
            cases hi₂ with
            | intro hi₂a hi₂b =>
              have h₄ : j * j ≤ i := hi₁a.1
              have h₅ : i < (j + 1) * (j + 1) := hi₁a.2
              have h₆ : j' * j' ≤ i := hi₂a.1
              have h₇ : i < (j' + 1) * (j' + 1) := hi₂a.2
              have h₈ : j < j' ∨ j' < j := by
                cases' lt_or_gt_of_ne h₂ with h_lt h_gt
                · left
                  exact h_lt
                · right
                  exact h_gt
              cases' h₈ with h_lt h_gt
              · have h₉ : (j + 1) * (j + 1) ≤ j' * j' := by
                  have h₁₀ : j + 1 ≤ j' := by linarith
                  nlinarith
                linarith
              · have h₉ : (j' + 1) * (j' + 1) ≤ j * j := by
                  have h₁₀ : j' + 1 ≤ j := by linarith
                  nlinarith
                linarith
      simp_all [h₃]
    · intro j hj
      intro j' hj' h_int
      have h₂ : j ≠ j' := by
        intro h_eq
        rw [h_eq] at h_int
        simp at h_int
      have h₃ : Disjoint (Ico (j * j) ((j + 1) * (j + 1)) ∩ Ico 1 (k + 1)) 
                 (Ico (j' * j') ((j' + 1) * (j' + 1)) ∩ Ico 1 (k + 1)) := by
        apply Finset.disjoint_left.mpr
        intro i hi
        simp only [Finset.mem_inter, Finset.mem_Ico] at hi ⊢
        cases hi with
        | intro hi₁ hi₂ =>
          cases hi₁ with
          | intro hi₁a hi₁b =>
            cases hi₂ with
            | intro hi₂a hi₂b =>
              have h₄ : j * j ≤ i := hi₁a.1
              have h₅ : i < (j + 1) * (j + 1) := hi₁a.2
              have h₆ : j' * j' ≤ i := hi₂a.1
              have h₇ : i < (j' + 1) * (j' + 1) := hi₂a.2
              have h₈ : j < j' ∨ j' < j := by
                cases' lt_or_gt_of_ne h₂ with h_lt h_gt
                · left
                  exact h_lt
                · right
                  exact h_gt
              cases' h₈ with h_lt h_gt
              · have h₉ : (j + 1) * (j + 1) ≤ j' * j' := by
                  have h₁₀ : j + 1 ≤ j' := by linarith
                  nlinarith
                linarith
              · have h₉ : (j' + 1) * (j' + 1) ≤ j * j := by
                  have h₁₀ : j' + 1 ≤ j := by linarith
                  nlinarith
                linarith
      simp_all [h₃]
  
  -- Bound each block
  have h_total_bound : ∑ j ∈ Ico 1 (m + 1), ∑ i ∈ Ico (j * j) ((j + 1) * (j + 1)) ∩ Ico 1 (k + 1), x i / (i : ℝ) ≤ 3 := by
    calc
      ∑ j ∈ Ico 1 (m + 1), ∑ i ∈ Ico (j * j) ((j + 1) * (j + 1)) ∩ Ico 1 (k + 1), x i / (i : ℝ) ≤
        ∑ j ∈ Ico 1 (m + 1), ∑ i ∈ Ico (j * j) ((j + 1) * (j + 1)), x i / (i : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        have h₁ : Ico (j * j) ((j + 1) * (j + 1)) ∩ Ico 1 (k + 1) ⊆ Ico (j * j) ((j + 1) * (j + 1)) := by
          intro i hi
          exact hi.1
        have h₂ : ∑ i ∈ Ico (j * j) ((j + 1) * (j + 1)) ∩ Ico 1 (k + 1), x i / (i : ℝ) ≤ 
          ∑ i ∈ Ico (j * j) ((j + 1) * (j + 1)), x i / (i : ℝ) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg h₁
          intro i hi
          have h₃ : 0 < (i : ℝ) := by
            have h₄ : j * j ≤ i := hi.1
            have h₅ : 0 < j := by
              have h₆ : 1 ≤ j := hj.1
              linarith
            have h₆ : 0 < j * j := by positivity
            linarith
          have h₄ : 0 < x i := hpos i
          positivity
        exact h₂
      _ = ∑ j ∈ Ico 1 (m + 1), ∑ i ∈ Ico (j * j) ((j + 1) * (j + 1)), x i / (i : ℝ) := by rfl
      _ ≤ ∑ j ∈ Ico 1 (m + 1), x (j * j) * ∑ i ∈ Ico (j * j) ((j + 1) * (j + 1)), (1 : ℝ) / (i : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        have h₁ : 1 ≤ j := hj.1
        have h₂ : ∑ i ∈ Ico (j * j) ((j + 1) * (j + 1)), x i / (i : ℝ) ≤ 
          x (j * j) * ∑ i ∈ Ico (j * j) ((j + 1) * (j + 1)), (1 : ℝ) / (i : ℝ) := h_block_bound j h₁
        exact h₂
      _ ≤ ∑ j ∈ Ico 1 (m + 1), x (j * j) * (2 / (j : ℝ)) := by
        apply Finset.sum_le_sum
        intro j hj
        have h₁ : 1 ≤ j := hj.1
        have h₂ : ∑ i ∈ Ico (j * j) ((j + 1) * (j + 1)), (1 : ℝ) / (i : ℝ) ≤ 2 / (j : ℝ) := h_harmonic_bound j h₁
        have h₃ : 0 < x (j * j) := hpos (j * j)
        have h₄ : 0 < (2 : ℝ) / (j : ℝ) := by
          have h₅ : 0 < (j : ℝ) := by exact_mod_cast (by linarith)
          positivity
        have h₅ : 0 ≤ x (j * j) := by linarith
        nlinarith
      _ = 2 * ∑ j ∈ Ico 1 (m + 1), x (j * j) / (j : ℝ) := by
        calc
          ∑ j ∈ Ico 1 (m + 1), x (j * j) * (2 / (j : ℝ)) = 
            ∑ j ∈ Ico 1 (m + 1), 2 * (x (j * j) / (j : ℝ)) := by
            apply Finset.sum_congr rfl
            intro j hj
            field_simp
            <;> ring_nf
          _ = 2 * ∑ j ∈ Ico 1 (m + 1), x (j * j) / (j : ℝ) := by
            simp [Finset.mul_sum]
      _ ≤ 2 * 1 := by
        have h₁ : ∑ j ∈ Ico 1 (m + 1), x (j * j) / (j : ℝ) ≤ 1 := by
          have h₂ : (Ico 1 (m + 1)).sum (fun i => x (i * i) / (i : ℝ)) ≤ 1 := hsq m
          exact h₂
        nlinarith
      _ = 2 := by norm_num
      _ ≤ 3 := by norm_num
  
  rw [h_decomp]
  exact h_total_bound
