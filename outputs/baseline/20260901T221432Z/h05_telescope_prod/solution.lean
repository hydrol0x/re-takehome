import Mathlib

open Finset
open scoped Nat

/-- Telescoping product: `∏_{k=2}^n (1 - 1/k²) = (n+1)/(2n)` for `n ≥ 2`. -/
theorem h05_telescope_prod (n : ℕ) (hn : 2 ≤ n) :
    ∏ k ∈ Icc 2 n, ((1 : ℝ) - 1 / (k : ℝ) ^ 2) = ((n : ℝ) + 1) / (2 * (n : ℝ)) := by
  -- rewrite each factor
  have h_factor (k : ℕ) (hk : k ∈ Icc 2 n) :
      (1 - (1 : ℝ) / (k : ℝ) ^ 2) =
        ((k : ℝ) - 1) / (k : ℝ) * ((k : ℝ) + 1) / (k : ℝ) := by
    have hk0 : (k : ℝ) ≠ 0 := by
      have hpos : (0 : ℝ) < (k : ℝ) := by
        have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
        have : (0 : ℝ) < (2 : ℝ) := by norm_num
        exact lt_of_lt_of_le this ‹_›
      exact ne_of_gt hpos
    field_simp [pow_two, hk0]
  -- split the product
  have hprod :
      ∏ k ∈ Icc 2 n, (1 - (1 : ℝ) / (k : ℝ) ^ 2) =
        (∏ k ∈ Icc 2 n, ((k : ℝ) - 1) / (k : ℝ)) *
        (∏ k ∈ Icc 2 n, ((k : ℝ) + 1) / (k : ℝ)) := by
    calc
      ∏ k ∈ Icc 2 n, (1 - (1 : ℝ) / (k : ℝ) ^ 2)
          = ∏ k ∈ Icc 2 n,
              (((k : ℝ) - 1) / (k : ℝ) * ((k : ℝ) + 1) / (k : ℝ)) := by
                apply prod_congr rfl
                intro k hk
                simpa [h_factor k hk]
      _ = (∏ k ∈ Icc 2 n, ((k : ℝ) - 1) / (k : ℝ)) *
          (∏ k ∈ Icc 2 n, ((k : ℝ) + 1) / (k : ℝ)) := by
            simpa using
              (Finset.prod_mul_distrib
                (s := Icc 2 n)
                (f := fun k => ((k : ℝ) - 1) / (k : ℝ))
                (g := fun k => ((k : ℝ) + 1) / (k : ℝ)))
  -- evaluate the first product
  have h_one_div :
      (∏ k ∈ Icc 2 n, ((k : ℝ) - 1) / (k : ℝ)) = (1 : ℝ) / (n : ℝ) := by
    have : (∏ k ∈ Icc 2 n, ((k : ℝ) - 1) / (k : ℝ)) =
        (∏ k ∈ Icc 2 n, ((k : ℝ) - 1)) / (∏ k ∈ Icc 2 n, (k : ℝ)) := by
      simp [div_eq_mul_inv, Finset.prod_mul_distrib]
    -- compute the two separate products
    have hnum :
        ∏ k ∈ Icc 2 n, ((k : ℝ) - 1) = ∏ j ∈ Icc 1 (n - 1), (j : ℝ) := by
      have : (Icc 2 n).map
          (Function.Embedding.mk (fun k : ℕ => k - 1) (by
            intro a b h; exact Nat.sub_eq_iff_eq_add.1 h)) = Icc 1 (n - 1) := by
        ext j
        constructor
        · intro hj
          rcases mem_map.1 hj with ⟨k, hk, rfl⟩
          rcases hk with ⟨h2k, hk⟩
          have : 1 ≤ k - 1 := Nat.succ_le_iff.1 (by
            have : 2 ≤ k := h2k
            exact Nat.succ_le_of_lt (Nat.lt_of_lt_of_le (Nat.succ_pos 0) this))
          have : k - 1 ≤ n - 1 := Nat.sub_le_sub_right hk 1
          exact ⟨this, this⟩
        · intro hj
          rcases hj with ⟨h1j, hjn⟩
          have hk : 2 ≤ j + 1 := Nat.succ_le_succ (Nat.succ_le_iff.2 h1j)
          have hkn : j + 1 ≤ n := Nat.succ_le_iff.2 hjn
          have : (j + 1) ∈ Icc 2 n := ⟨hk, hkn⟩
          exact mem_map.2 ⟨j + 1, this, by simp⟩
      simpa [this] using
        (prod_image (s := Icc 2 n) (f := fun k : ℕ => (k : ℝ) - 1)
          (inj := fun a b h => by
            have : (a : ℝ) = b := by
              have : (a : ℝ) - 1 = (b : ℝ) - 1 := by simpa using h
              linarith
            exact Nat.cast_inj.1 this)).symm
    have hden :
        ∏ k ∈ Icc 2 n, (k : ℝ) = (∏ j ∈ Icc 1 n, (j : ℝ)) / (1 : ℝ) := by
      simp
    have : (∏ k ∈ Icc 2 n, ((k : ℝ) - 1)) / (∏ k ∈ Icc 2 n, (k : ℝ)) =
        (∏ j ∈ Icc 1 (n - 1), (j : ℝ)) / (∏ j ∈ Icc 1 n, (j : ℝ)) := by
      simpa [hnum, hden]
    have : (∏ j ∈ Icc 1 (n - 1), (j : ℝ)) / (∏ j ∈ Icc 1 n, (j : ℝ)) = (1 : ℝ) / (n : ℝ) := by
      have hpos : (n : ℝ) ≠ 0 := by
        have : (0 : ℝ) < (n : ℝ) := by
          have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          have : (0 : ℝ) < (2 : ℝ) := by norm_num
          exact lt_of_lt_of_le this ‹_›
        exact ne_of_gt this
      have : (∏ j ∈ Icc 1 n, (j : ℝ)) = (∏ j ∈ Icc 1 (n - 1), (j : ℝ)) * (n : ℝ) := by
        have : Icc 1 n = insert n (Icc 1 (n - 1)) := by
          ext j
          constructor
          · intro hj
            rcases hj with ⟨h1j, hjn⟩
            by_cases h : j = n
            · simp [h]
            · have : j ≤ n - 1 := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hjn h)
              have : 1 ≤ j := h1j
              have : j ∈ Icc 1 (n - 1) := ⟨this, this⟩
              simp [h, this]
          · intro hj
            rcases mem_insert.1 hj with h | h
            · simp [h]
            · rcases h with ⟨h1j, hjn⟩
              exact ⟨h1j, Nat.le_succ_of_le hjn⟩
        simpa [this, prod_insert (by
          have : n ∉ Icc 1 (n - 1) := by
            have : n ≤ n - 1 → False := by
              intro hle; exact Nat.not_succ_le_self _ (Nat.succ_le_of_lt (Nat.lt_of_lt_of_le (Nat.succ_pos _) hle))
            exact not_false.mpr (by
              intro hmem; exact this (by
                rcases hmem with ⟨h1n, hnn⟩; exact hnn)))
          ] using rfl
      simpa [this, mul_comm, mul_left_comm, mul_assoc, div_mul_eq_mul_div, hpos] using rfl
    simpa [this] using this
  -- evaluate the second product
  have h_two_div :
      (∏ k ∈ Icc 2 n, ((k : ℝ) + 1) / (k : ℝ)) = ((n : ℝ) + 1) / 2 := by
    have : (∏ k ∈ Icc 2 n, ((k : ℝ) + 1) / (k : ℝ)) =
        (∏ k ∈ Icc 2 n, ((k : ℝ) + 1)) / (∏ k ∈ Icc 2 n, (k : ℝ)) := by
      simp [div_eq_mul_inv, Finset.prod_mul_distrib]
    have hnum :
        ∏ k ∈ Icc 2 n, ((k : ℝ) + 1) = ∏ j ∈ Icc 3 (n + 1), (j : ℝ) := by
      have : (Icc 2 n).map
          (Function.Embedding.mk (fun k : ℕ => k + 1) (by
            intro a b h; exact Nat.add_left_cancel h)) = Icc 3 (n + 1) := by
        ext j
        constructor
        · intro hj
          rcases mem_map.1 hj with ⟨k, hk, rfl⟩
          rcases hk with ⟨h2k, hkn⟩
          exact ⟨Nat.succ_le_succ h2k, Nat.succ_le_succ hkn⟩
        · intro hj
          rcases hj with ⟨h3j, hjn⟩
          have hk : 2 ≤ j - 1 := Nat.succ_le_iff.1 (by
            have : 3 ≤ j := h3j
            exact Nat.succ_le_of_lt (Nat.lt_of_lt_of_le (Nat.succ_pos 1) this))
          have hkn : j - 1 ≤ n := Nat.sub_le_iff_le_add.2 (by
            have : j ≤ n + 1 := hjn
            exact Nat.le_of_succ_le_succ this)
          have : (j - 1) ∈ Icc 2 n := ⟨hk, hkn⟩
          exact mem_map.2 ⟨j - 1, this, by simp⟩
      simpa [this] using
        (prod_image (s := Icc 2 n) (f := fun k : ℕ => (k : ℝ) + 1)
          (inj := fun a b h => by
            have : (a : ℝ) = b := by
              have : (a : ℝ) + 1 = (b : ℝ) + 1 := by simpa using h
              linarith
            exact Nat.cast_inj.1 this)).symm
    have hden :
        ∏ k ∈ Icc 2 n, (k : ℝ) = (∏ j ∈ Icc 1 n, (j : ℝ)) / (1 : ℝ) := by
      simp
    have : (∏ k ∈ Icc 2 n, ((k : ℝ) + 1)) / (∏ k ∈ Icc 2 n, (k : ℝ)) =
        (∏ j ∈ Icc 3 (n + 1), (j : ℝ)) / (∏ j ∈ Icc 1 n, (j : ℝ)) := by
      simpa [hnum, hden]
    have : (∏ j ∈ Icc 3 (n + 1), (j : ℝ)) / (∏ j ∈ Icc 1 n, (j : ℝ)) = ((n : ℝ) + 1) / 2 := by
      have hpos : (2 : ℝ) ≠ 0 := by norm_num
      have : (∏ j ∈ Icc 1 n, (j : ℝ)) = (∏ j ∈ Icc 1 (n + 1), (j : ℝ)) / ((n + 1 : ℝ)) := by
        have : Icc 1 (n + 1) = insert (n + 1) (Icc 1 n) := by
          ext j
          constructor
          · intro hj
            rcases hj with ⟨h1j, hjn⟩
            by_cases h : j = n + 1
            · simp [h]
            · have : j ≤ n := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hjn h)
              exact mem_insert.2 (Or.inr ⟨h1j, this⟩)
          · intro hj
            rcases mem_insert.1 hj with h | h
            · simp [h]
            · rcases h with ⟨h1j, hjn⟩
              exact ⟨h1j, Nat.le_succ_of_le hjn⟩
        simpa [this, prod_insert (by
          have : (n + 1) ∉ Icc 1 n := by
            intro hmem; rcases hmem with ⟨_, hle⟩; exact Nat.not_succ_le_self _ hle
          )] using rfl
      have : (∏ j ∈ Icc 3 (n + 1), (j : ℝ)) =
          (∏ j ∈ Icc 1 (n + 1), (j : ℝ)) / ((1 : ℝ) * (2 : ℝ)) := by
        have : Icc 1 (n + 1) = insert 1 (insert 2 (Icc 3 (n + 1))) := by
          ext j
          constructor
          · intro hj
            rcases hj with ⟨h1j, hjn⟩
            by_cases h12 : j = 1 ∨ j = 2
            · rcases h12 with h | h
              · left; simp [h]
              · right; left; simp [h]
            · right; right
              have : 3 ≤ j := Nat.succ_le_of_lt (Nat.lt_of_le_of_ne h1j (by
                intro h; cases h12; cases h; cases h))
              exact ⟨this, hjn⟩
          · intro hj
            rcases hj with h | h | h
            · rcases h with rfl; exact ⟨by norm_num, Nat.succ_le_succ (Nat.zero_le _)⟩
            · rcases h with rfl; exact ⟨by norm_num, Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _))⟩
            · rcases h with ⟨h3j, hjn⟩
              exact ⟨Nat.succ_le_of_lt (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_one))), Nat.le_of_lt_succ hjn⟩
        simpa [this, prod_insert (by
          have : (1 : ℕ) ∉ Icc 3 (n + 1) := by
            intro hmem; rcases hmem with ⟨h1, _⟩; exact Nat.not_lt_zero _ (by linarith)
          ), prod_insert (by
            have : (2 : ℕ) ∉ Icc 3 (n + 1) := by
              intro hmem; rcases hmem with ⟨h2, _⟩; exact Nat.not_lt_zero _ (by linarith)
            )] using rfl
      have : (∏ j ∈ Icc 3 (n + 1), (j : ℝ)) / (∏ j ∈ Icc 1 n, (j : ℝ)) =
          ((n + 1 : ℝ) / (2 : ℝ)) := by
        have h2 : (∏ j ∈ Icc 1 (n + 1), (j : ℝ)) / (∏ j ∈ Icc 1 n, (j : ℝ)) = (n + 1 : ℝ) := by
          simpa [prod_Icc_succ_top] using rfl
        have h3 : (∏ j ∈ Icc 3 (n + 1), (j : ℝ)) = (∏ j ∈ Icc 1 (n + 1), (j : ℝ)) / (1 : ℝ) / (2 : ℝ) := by
          simpa using rfl
        simpa [h2, h3, div_mul_eq_mul_div, mul_comm, mul_left_comm, mul_assoc] using rfl
      simpa using this
    simpa [this] using this
  -- combine the two evaluated products
  have : ∏ k ∈ Icc 2 n, (1 - (1 : ℝ) / (k : ℝ) ^ 2) =
      ((1 : ℝ) / (n : ℝ)) * (((n : ℝ) + 1) / 2) := by
    simpa [h_one_div, h_two_div, mul_comm, mul_left_comm, mul_assoc] using hprod
  simpa [div_mul_eq_mul_div, mul_comm, mul_left_comm, mul_assoc] using this
