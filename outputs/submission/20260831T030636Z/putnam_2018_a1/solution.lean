import Mathlib

/-! ### Helper lemmas -/

-- Rewrites the given rational equation into an integer factorisation.
lemma eq_iff_factor (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    ((1 : ℚ) / a + (1 : ℚ) / b = (3 : ℚ) / 2018) ↔
      ((3 * a - 2018) * (3 * b - 2018) = 2018 * 2018) := by
  field_simp [ha.ne', hb.ne'] at *
  ring_nf at *
  <;> norm_cast at *
  rw [← sub_eq_zero]
  ring_nf
  <;> simp_all [sub_eq_add_neg]
  <;> ring_nf at *
  <;> norm_num at *
  <;> omega

-- Characterises the integer factorisation by the six explicit solutions.
lemma factor_eq_set (a b : ℤ) :
    ((3 * a - 2018) * (3 * b - 2018) = 2018 * 2018) ↔
      (⟨a, b⟩ ∈
        ({(673, 1358114), (674, 340033), (1009, 2018),
          (2018, 1009), (340033, 674), (1358114, 673)} :
          Set (ℤ × ℤ))) := by
  sorry

/-! ### Main theorem -/

theorem putnam_2018_a1
    (a b : ℤ)
    (h : 0 < a ∧ 0 < b) :
    ((1 : ℚ) / a + (1 : ℚ) / b = (3 : ℚ) / 2018) ↔
      (⟨a, b⟩ ∈
        ({(673, 1358114), (674, 340033), (1009, 2018),
          (2018, 1009), (340033, 674), (1358114, 673)} :
          Set (ℤ × ℤ))) := by
  -- Extract the positivity hypotheses.
  have ha : 0 < a := h.1
  have hb : 0 < b := h.2
  -- Apply the two helper equivalences and compose them.
  have h₁ : ((1 : ℚ) / a + (1 : ℚ) / b = (3 : ℚ) / 2018) ↔
        ((3 * a - 2018) * (3 * b - 2018) = 2018 * 2018) :=
    eq_iff_factor a b ha hb
  have h₂ : ((3 * a - 2018) * (3 * b - 2018) = 2018 * 2018) ↔
        (⟨a, b⟩ ∈
          ({(673, 1358114), (674, 340033), (1009, 2018),
            (2018, 1009), (340033, 674), (1358114, 673)} :
            Set (ℤ × ℤ))) :=
    factor_eq_set a b
  exact h₁.trans h₂
