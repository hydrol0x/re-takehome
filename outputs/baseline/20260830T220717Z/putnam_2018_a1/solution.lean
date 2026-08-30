import Mathlib.Tactic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.GCD
import Mathlib.Data.Set.Lattice

open Set

theorem putnam_2018_a1
  (a b : ℤ)
  (h : 0 < a ∧ 0 < b) :
  ((1 : ℚ) / a + (1 : ℚ) / b = (3 : ℚ) / 2018) ↔
    (⟨a, b⟩ ∈ ({(673, 1358114), (674, 340033), (1009, 2018),
      (2018, 1009), (340033, 674), (1358114, 673)} : Set (ℤ × ℤ))) := by
  constructor
  · intro h_eq
    have ha₀ : (a : ℚ) ≠ 0 := by
      exact_mod_cast (ne_of_gt h.1)
    have hb₀ : (b : ℚ) ≠ 0 := by
      exact_mod_cast (ne_of_gt h.2)
    -- turn the rational equation into an integer one
    have h_int : (a + b) * 2018 = 3 * a * b := by
      have := h_eq
      field_simp [ha₀, hb₀] at this
      have : ((a + b) * 2018 : ℚ) = (3 * a * b : ℚ) := by
        simpa using this
      exact_mod_cast this
    -- factorisation
    have h_factor : (3 * a - 2018) * (3 * b - 2018) = 2018 ^ 2 := by
      have : (3 * a - 2018) * (3 * b - 2018) =
          9 * a * b - 3 * 2018 * (a + b) + 2018 ^ 2 := by
        ring
      have h9 : 9 * a * b = 3 * 2018 * (a + b) := by
        have := h_int
        have := congrArg (fun t : ℤ => 3 * t) this
        simpa [mul_comm, mul_left_comm, mul_assoc, mul_add, add_mul] using this.symm
      simpa [this, h9] using this
    -- positivity of the factors
    have hx_pos : 0 < 3 * a - 2018 := by
      have : (1 : ℚ) / a ≤ (3 : ℚ) / 2018 := by
        have : (1 : ℚ) / a + (1 : ℚ) / b = (3 : ℚ) / 2018 := h_eq
        have : (1 : ℚ) / a ≤ (3 : ℚ) / 2018 := by
          have : (1 : ℚ) / a ≤ (1 : ℚ) / a + (1 : ℚ) / b := by
            have : (0 : ℚ) ≤ (1 : ℚ) / b := by
              have : (0 : ℚ) < (b : ℚ) := by exact_mod_cast h.2
              exact inv_nonneg.mpr (le_of_lt this)
            linarith
          linarith [h_eq]
        exact this
      have : (a : ℚ) ≥ (2018 : ℚ) / 3 := by
        have : (1 : ℚ) / a ≤ (3 : ℚ) / 2018 := by
          simpa using this
        have : (a : ℚ) ≥ (2018 : ℚ) / 3 := by
          have hpos : (0 : ℚ) < (a : ℚ) := by exact_mod_cast h.1
          have := inv_le_inv_of_le hpos (by
            have : (0 : ℚ) < (2018 : ℚ) / 3 := by norm_num
            exact this) this
          simpa [one_div] using this
        exact this
      have : (3 : ℚ) * (a : ℚ) - 2018 > (0 : ℚ) := by
        have : (3 : ℚ) * (a : ℚ) > 2018 := by
          have : (a : ℚ) ≥ (2018 : ℚ) / 3 := by exact this
          linarith
        linarith
      exact_mod_cast this
    have hy_pos : 0 < 3 * b - 2018 := by
      have : (3 * a - 2018) * (3 * b - 2018) = 2018 ^ 2 := h_factor
      have : 0 < (3 * a - 2018) := hx_pos
      have : 0 < (3 * b - 2018) := by
        have : (0 : ℤ) < 2018 ^ 2 := by norm_num
        have : (0 : ℤ) < (3 * a - 2018) * (3 * b - 2018) := by
          simpa [h_factor] using this
        have : 0 < (3 * b - 2018) := by
          have : (3 * a - 208) > 0 := hx_pos
          have : (3 * a - 2018) * (3 * b - 2018) > 0 := by
            simpa [h_factor] using this
          exact mul_pos.mp this).2
        exact this
    -- the only positive divisors of 2018^2 that are ≡ 1 [ZMOD 3] are
    have hdiv :
        (3 * a - 2018) ∈ ({1, 4, 1009, 4036, 1018081, 2018 ^ 2} : Set ℤ) := by
      have hpos : 0 < 3 * a - 2018 := hx_pos
      have hmod : (3 * a - 2018) ≡ 1 [ZMOD 3] := by
        have : (3 * a : ℤ) ≡ 0 [ZMOD 3] := by
          simpa using (dvd_refl 3).modEq_zero
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          this.sub (by norm_num : (2018 : ℤ) ≡ 2 [ZMOD 3])
      have hdivs : (3 * a - 2018) ∣ 2018 ^ 2 := by
        have : (3 * a - 2018) * (3 * b - 2018) = 2018 ^ 2 := h_factor
        exact ⟨3 * b - 2018, by simpa [mul_comm] using this⟩
      have : (3 * a - 2018) ∈ ({1, 4, 1009, 4036, 1018081, 2018 ^ 2} : Set ℤ) := by
        have hlist : List ℤ := [1, 4, 1009, 4036, 1018081, 2018 ^ 2]
        have : (3 * a - 2018) ∈ (Set.ofList hlist) := by
          rcases (Nat.mem_factors (Nat.abs (3 * a - 2018)) (by
            have : (3 * a - 2018) ≠ 0 := by
              have : (0 : ℤ) < 3 * a - 2018 := hx_pos; exact ne_of_gt this
            exact this)) with ⟨d, hd⟩
          sorry
        exact this
      exact this
    rcases hdiv with h1 | h1 | h1 | h1 | h1 | h1
    · -- case 1
      left
      have : a = 673 := by
        have : 3 * a - 2018 = 1 := h1
        linarith
      have : b = 1358114 := by
        have : (3 * b - 2018) = 2018 ^ 2 := by
          have : (3 * a - 2018) * (3 * b - 2018) = 2018 ^ 2 := h_factor
          simpa [h1] using this
        linarith
      simpa [this, ‹a = 673›, ‹b = 1358114›]
    · -- case 4
      right; left
      have : a = 674 := by
        have : 3 * a - 2018 = 4 := h1
        linarith
      have : b = 340033 := by
        have : (3 * b - 2018) = 1018081 := by
          have : (3 * a - 2018) * (3 * b - 2018) = 2018 ^ 2 := h_factor
          simpa [h1] using this
        linarith
      simpa [this, ‹a = 674›, ‹b = 340033›]
    · -- case 1009
      right; right; left
      have : a = 1009 := by
        have : 3 * a - 2018 = 1009 := h1
        linarith
      have : b = 2018 := by
        have : (3 * b - 2018) = 4036 := by
          have : (3 * a - 2018) * (3 * b - 2018) = 2018 ^ 2 := h_factor
          simpa [h1] using this
        linarith
      simpa [this, ‹a = 1009›, ‹b = 2018›]
    · -- case 4036
      right; right; right; left
      have : a = 2018 := by
        have : 3 * a - 2018 = 4036 := h1
        linarith
      have : b = 1009 := by
        have : (3 * b - 2018) = 1009 := by
          have : (3 * a - 2018) * (3 * b - 2018) = 2018 ^ 2 := h_factor
          simpa [h1] using this
        linarith
      simpa [this, ‹a = 2018›, ‹b = 1009›]
    · -- case 1018081
      right; right; right; right; left
      have : a = 340033 := by
        have : 3 * a - 2018 = 1018081 := h1
        linarith
      have : b = 674 := by
        have : (3 * b - 2018) = 4 := by
          have : (3 * a - 2018) * (3 * b - 2018) = 2018 ^ 2 := h_factor
          simpa [h1] using this
        linarith
      simpa [this, ‹a = 340033›, ‹b = 674›]
    · -- case 2018^2
      right; right; right; right; right
      have : a = 1358114 := by
        have : 3 * a - 2018 = 2018 ^ 2 := h1
        linarith
      have : b = 673 := by
        have : (3 * b - 2018) = 1 := by
          have : (3 * a - 2018) * (3 * b - 2018) = 2018 ^ 2 := h_factor
          simpa [h1] using this
        linarith
      simpa [this, ‹a = 1358114›, ‹b = 673›]
  · intro hmem
    rcases hmem with hmem | hmem | hmem | hmem | hmem | hmem
    · -- (673,1358114)
      have ha : a = 673 := by
        have : (a, b) = (673, 1358114) := hmem
        cases this; rfl
      have hb : b = 1358114 := by
        have : (a, b) = (673, 1358114) := hmem
        cases this; rfl
      subst_vars
      norm_num
    · -- (674,340033)
      have ha : a = 674 := by
        have : (a, b) = (674, 340033) := hmem
        cases this; rfl
      have hb : b = 340033 := by
        have : (a, b) = (674, 340033) := hmem
        cases this; rfl
      subst_vars
      norm_num
    · -- (1009,2018)
      have ha : a = 1009 := by
        have : (a, b) = (1009, 2018) := hmem
        cases this; rfl
      have hb : b = 2018 := by
        have : (a, b) = (1009, 2018) := hmem
        cases this; rfl
      subst_vars
      norm_num
    · -- (2018,1009)
      have ha : a = 2018 := by
        have : (a, b) = (2018, 1009) := hmem
        cases this; rfl
      have hb : b = 1009 := by
        have : (a, b) = (2018, 1009) := hmem
        cases this; rfl
      subst_vars
      norm_num
    · -- (340033,674)
      have ha : a = 340033 := by
        have : (a, b) = (340033, 674) := hmem
        cases this; rfl
      have hb : b = 674 := by
        have : (a, b) = (340033, 674) := hmem
        cases this; rfl
      subst_vars
      norm_num
    · -- (1358114,673)
      have ha : a = 1358114 := by
        have : (a, b) = (1358114, 673) := hmem
        cases this; rfl
      have hb : b = 673 := by
        have : (a, b) = (1358114, 673) := hmem
        cases this; rfl
      subst_vars
      norm_num
