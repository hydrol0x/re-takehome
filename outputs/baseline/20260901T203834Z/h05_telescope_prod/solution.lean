import Mathlib

/-- Telescoping product: `∏_{k=2}^n (1 - 1/k²) = (n+1)/(2n)` for `n ≥ 2`. -/
theorem h05_telescope_prod (n : ℕ) (hn : 2 ≤ n) :
    ∏ k ∈ Finset.Icc 2 n, ((1 : ℝ) - 1 / (k : ℝ) ^ 2) = ((n : ℝ) + 1) / (2 * (n : ℝ)) := by
  -- rewrite each factor
  have h_factor :
      ∀ k : ℕ, (2 ≤ k) →
        (1 : ℝ) - 1 / (k : ℝ) ^ 2 = ((k - 1 : ℝ) / k) * ((k + 1 : ℝ) / k) := by
    intro k hk
    have hkpos : (0 : ℝ) < (k : ℝ) := by
      have : (0 : ℕ) < k := Nat.pos_of_ne_zero (Nat.ne_of_gt (Nat.succ_lt_succ (Nat.succ_lt_succ (Nat.zero_lt_one))))
      exact_mod_cast this
    have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hkpos
    field_simp [pow_two, hk_ne] ; ring
  -- turn the product into a product of two simpler products
  have h_prod :
      (∏ k ∈ Finset.Icc 2 n, ((1 : ℝ) - 1 / (k : ℝ) ^ 2)) =
        (∏ k ∈ Finset.Icc 2 n, ((k - 1 : ℝ) / k)) *
        (∏ k ∈ Finset.Icc 2 n, ((k + 1 : ℝ) / k)) := by
    calc
      ∏ k ∈ Finset.Icc 2 n, ((1 : ℝ) - 1 / (k : ℝ) ^ 2)
          = ∏ k ∈ Finset.Icc 2 n,
              ((k - 1 : ℝ) / k) * ((k + 1 : ℝ) / k) := by
                refine Finset.prod_congr rfl ?_
                intro k hk
                have hk2 : (2 : ℕ) ≤ k := (Finset.mem_Icc.1 hk).1
                simpa using h_factor k hk2
      _ = (∏ k ∈ Finset.Icc 2 n, ((k - 1 : ℝ) / k)) *
          (∏ k ∈ Finset.Icc 2 n, ((k + 1 : ℝ) / k)) :=
            (Finset.prod_mul_distrib _ _ _)
  -- evaluate the two products separately
  have h_left :
      ∏ k ∈ Finset.Icc 2 n, ((k - 1 : ℝ) / k) = (1 : ℝ) / n := by
    have : (∏ k ∈ Finset.Icc 2 n, ((k - 1 : ℝ) / k)) =
        (∏ k ∈ Finset.Icc 1 (n - 1), (k : ℝ)) *
        (∏ k ∈ Finset.Icc 2 n, (k : ℝ))⁻¹ := by
      calc
        ∏ k ∈ Finset.Icc 2 n, ((k - 1 : ℝ) / k)
            = ∏ k ∈ Finset.Icc 2 n, ((k - 1 : ℝ) * (k : ℝ)⁻¹) := by
                simp [div_eq_mul_inv]
        _ = (∏ k ∈ Finset.Icc 2 n, (k - 1 : ℝ)) *
            (∏ k ∈ Finset.Icc 2 n, (k : ℝ)⁻¹) := (Finset.prod_mul_distrib _ _ _)
        _ = (∏ k ∈ Finset.Icc 2 n, (k - 1 : ℝ)) *
            (∏ k ∈ Finset.Icc 2 n, (k : ℝ))⁻¹ := by
                simp [div_eq_mul_inv]
      have h1 :
          ∏ k ∈ Finset.Icc 2 n, (k - 1 : ℝ) =
            ∏ k ∈ Finset.Icc 1 (n - 1), (k : ℝ) := by
        refine Finset.prod_bij (fun k hk => k - 1) ?_ ?_ ?_ ?_
        · intro k hk; 
          have hk' := (Finset.mem_Icc.1 hk).1
          have hk'' := (Finset.mem_Icc.1 hk).2
          have : 1 ≤ k - 1 := Nat.succ_le_iff.mp (Nat.succ_le_of_lt hk')
          have : (k - 1) ≤ n - 1 := Nat.sub_le_sub_right hk'' 1
          exact Finset.mem_Icc.2 ⟨this, by
            have : k - 1 ≤ n - 1 := Nat.sub_le_sub_right hk'' 1
            exact this⟩
        · intro a ha b hb h_eq; 
          have : a = b := by
            have : a + 1 = b + 1 := by
              simpa [Nat.add_sub_cancel] using congrArg (fun x => x + 1) h_eq
            exact Nat.succ_inj.mp this
          exact this
        · intro y hy; 
          rcases Finset.mem_Icc.1 hy with ⟨hy1, hy2⟩
          have : y + 1 ∈ Finset.Icc 2 n := by
            have hy1' : 2 ≤ y + 1 := Nat.succ_le_succ hy1
            have hy2' : y + 1 ≤ n := Nat.succ_le_iff.mp hy2
            exact Finset.mem_Icc.2 ⟨hy1', hy2'⟩
          exact ⟨y + 1, this, by simp⟩
        · intro y hy; rfl
      simpa [h1] using this
    have h2 :
        (∏ k ∈ Finset.Icc 2 n, (k : ℝ)) = (n : ℝ) ! := by
      -- factorial cast as product over 1..n
      have : (∏ k ∈ Finset.Icc 1 n, (k : ℝ)) = (n : ℝ)! := by
        simpa using (Nat.cast_prod (s := Finset.Icc 1 n) (f := fun k => (k : ℝ)))
      simpa [Finset.Icc_succ_left] using this
    have h3 :
        (∏ k ∈ Finset.Icc 1 (n - 1), (k : ℝ)) = ((n - 1) : ℝ)! := by
      simpa using (Nat.cast_prod (s := Finset.Icc 1 (n - 1)) (f := fun k => (k : ℝ)))
    have h4 : (n : ℝ)! / ((n - 1) : ℝ)! = (n : ℝ) := by
      have : ((n - 1) : ℝ)! * (n : ℝ) = (n : ℝ)! := by
        simpa using (Nat.cast_mul (a := (n - 1) !) (b := n) )
      field_simp [this]
    have : (∏ k ∈ Finset.Icc 2 n, ((k - 1 : ℝ) / k)) =
        ((n - 1) : ℝ)! * ((n : ℝ)!)⁻¹ := by
      simpa [h1, h2, h3] using this
    simpa [h4, div_eq_mul_inv] using this
  have h_right :
      ∏ k ∈ Finset.Icc 2 n, ((k + 1 : ℝ) / k) = (n + 1 : ℝ) / 2 := by
    have : (∏ k ∈ Finset.Icc 2 n, ((k + 1 : ℝ) / k)) =
        (∏ k ∈ Finset.Icc 3 (n + 1), (k : ℝ)) *
        (∏ k ∈ Finset.Icc 2 n, (k : ℝ))⁻¹ := by
      calc
        ∏ k ∈ Finset.Icc 2 n, ((k + 1 : ℝ) / k)
            = ∏ k ∈ Finset.Icc 2 n, ((k + 1 : ℝ) * (k : ℝ)⁻¹) := by
                simp [div_eq_mul_inv]
        _ = (∏ k ∈ Finset.Icc 2 n, (k + 1 : ℝ)) *
            (∏ k ∈ Finset.Icc 2 n, (k : ℝ)⁻¹) := (Finset.prod_mul_distrib _ _ _)
        _ = (∏ k ∈ Finset.Icc 2 n, (k + 1 : ℝ)) *
            (∏ k ∈ Finset.Icc 2 n, (k : ℝ))⁻¹ := by
                simp [div_eq_mul_inv]
      have hmap :
          ∏ k ∈ Finset.Icc 2 n, (k + 1 : ℝ) =
            ∏ k ∈ Finset.Icc 3 (n + 1), (k : ℝ) := by
        refine Finset.prod_bij (fun k hk => k + 1) ?_ ?_ ?_ ?_
        · intro k hk
          rcases Finset.mem_Icc.1 hk with ⟨hk2, hkn⟩
          have : 3 ≤ k + 1 := Nat.succ_le_succ hk2
          have : k + 1 ≤ n + 1 := Nat.succ_le_succ hkn
          exact Finset.mem_Icc.2 ⟨this, this⟩
        · intro a ha b hb h_eq
          have : a = b := by
            have : a + 1 = b + 1 := by simpa using congrArg (fun x => x - 1) h_eq
            exact Nat.succ_inj.mp this
          exact this
        · intro y hy
          rcases Finset.mem_Icc.1 hy with ⟨hy3, hyN⟩
          have : y - 1 ∈ Finset.Icc 2 n := by
            have hy2 : 2 ≤ y - 1 := Nat.succ_le_iff.mp hy3
            have hyn : y - 1 ≤ n := Nat.sub_le_iff_le_add'.mpr (by
              have : y ≤ n + 1 := hyN
              exact Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) this))
            exact Finset.mem_Icc.2 ⟨hy2, hyn⟩
          exact ⟨y - 1, this, by simp⟩
        · intro y hy; rfl
      simpa [hmap] using this
    have h2 :
        (∏ k ∈ Finset.Icc 2 n, (k : ℝ)) = (n : ℝ)! := by
      simpa using (Nat.cast_prod (s := Finset.Icc 2 n) (f := fun k => (k : ℝ)))
    have h3 :
        (∏ k ∈ Finset.Icc 3 (n + 1), (k : ℝ)) = ((n + 1) : ℝ)! / 2 := by
      have : (∏ k ∈ Finset.Icc 1 (n + 1), (k : ℝ)) = ((n + 1) : ℝ)! := by
        simpa using (Nat.cast_prod (s := Finset.Icc 1 (n + 1)) (f := fun k => (k : ℝ)))
      have htemp :
          (∏ k ∈ Finset.Icc 3 (n + 1), (k : ℝ)) =
            ((n + 1) : ℝ)! / (2 : ℝ) := by
        have : (∏ k ∈ Finset.Icc 1 (n + 1), (k : ℝ)) =
            (∏ k ∈ Finset.Icc 1 2, (k : ℝ)) *
            (∏ k ∈ Finset.Icc 3 (n + 1), (k : ℝ)) := by
          simpa [Finset.Icc_succ_left, Finset.Icc_succ_right, mul_comm, mul_left_comm, mul_assoc]
            using (Finset.prod_Icc_succ_top (a:=1) (b:=2) (f:=fun k => (k : ℝ)))
        have h12 : (∏ k ∈ Finset.Icc 1 2, (k : ℝ)) = (2 : ℝ) := by
          simp
        have : ((n + 1) : ℝ)! = (2 : ℝ) * (∏ k ∈ Finset.Icc 3 (n + 1), (k : ℝ)) := by
          simpa [h12] using this.symm
        field_simp [this]
      simpa using htemp
    have : (∏ k ∈ Finset.Icc 2 n, ((k + 1 : ℝ) / k)) =
        ((n + 1) : ℝ)! / (2 * (n : ℝ)!) := by
      simpa [h2, h3] using this
    have : ((n + 1) : ℝ)! / (2 * (n : ℝ)!) = (n + 1 : ℝ) / 2 := by
      have : ((n : ℝ)!) * ((n + 1) : ℝ) = ((n + 1) : ℝ)! := by
        simpa using (Nat.cast_mul (a := n !) (b := n + 1))
      field_simp [this]
    simpa [this]
  -- combine the two evaluated products
  have : ∏ k ∈ Finset.Icc 2 n, ((1 : ℝ) - 1 / (k : ℝ) ^ 2) =
      ((1 : ℝ) / n) * ((n + 1 : ℝ) / 2) := by
    simpa [h_left, h_right] using h_prod
  simpa [div_mul_eq_mul_div, mul_comm, mul_left_comm, mul_assoc] using this
