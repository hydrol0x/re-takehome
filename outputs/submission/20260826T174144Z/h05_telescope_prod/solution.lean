import Mathlib

/-- Algebraic identity: 1 - 1/k² = (k-1)/k · (k+1)/k for k ≥ 2 -/
lemma one_minus_inv_sq (k : ℕ) (hk : 2 ≤ k) :
    (1 : ℝ) - 1 / (k : ℝ) ^ 2 = (((k : ℝ) - 1) / (k : ℝ)) * (((k : ℝ) + 1) / (k : ℝ)) := by calc
        (1 : ℝ) - 1 / (k : ℝ) ^ 2 = ((k : ℝ) ^ 2 - 1) / (k : ℝ) ^ 2 := by
            field_simp [hk] <;> ring
        _ = (((k : ℝ) - 1) * ((k : ℝ) + 1)) / (k : ℝ) ^ 2 := by
            rw [show (k : ℝ) ^ 2 - 1 = ((k : ℝ) - 1) * ((k : ℝ) + 1) by ring]
        _ = (((k : ℝ) - 1) / (k : ℝ)) * (((k : ℝ) + 1) / (k : ℝ)) := by
            field_simp [hk] <;> ring

/-- First partial product: ∏_{k=2}^n (k-1)/k = 1/n -/
lemma first_half_product (n : ℕ) (hn : 2 ≤ n) :
    ∏ k ∈ Finset.Icc 2 n, ((k : ℝ) - 1) / (k : ℝ) = 1 / (n : ℝ) := by sorry

/-- Second partial product: ∏_{k=2}^n (k+1)/k = (n+1)/2 -/
lemma second_half_product (n : ℕ) (hn : 2 ≤ n) :
    ∏ k ∈ Finset.Icc 2 n, ((k : ℝ) + 1) / (k : ℝ) = ((n : ℝ) + 1) / 2 := by sorry

/-- Full telescoping product equals (n+1)/(2n) -/
lemma full_telescope_product (n : ℕ) (hn : 2 ≤ n) :
    ∏ k ∈ Finset.Icc 2 n, ((((k : ℝ) - 1) / (k : ℝ)) * (((k : ℝ) + 1) / (k : ℝ))) = ((n : ℝ) + 1) / (2 * (n : ℝ)) := by calc
        ∏ k ∈ Finset.Icc 2 n, ((((k : ℝ) - 1) / (k : ℝ)) * (((k : ℝ) + 1) / (k : ℝ))) 
            = (∏ k ∈ Finset.Icc 2 n, ((k : ℝ) - 1) / (k : ℝ)) * (∏ k ∈ Finset.Icc 2 n, ((k : ℝ) + 1) / (k : ℝ)) := by
            rw [Finset.prod_mul_distrib]
        _ = (1 / (n : ℝ)) * (((n : ℝ) + 1) / 2) := by
            rw [first_half_product n hn, second_half_product n hn]
        _ = ((n : ℝ) + 1) / (2 * (n : ℝ)) := by
            field_simp <;> ring

/-- Telescoping product identity: ∏_{k=2}^n (1 - 1/k²) = (n+1)/(2n) for n ≥ 2 -/
theorem h05_telescope_prod (n : ℕ) (hn : 2 ≤ n) :
    ∏ k ∈ Finset.Icc 2 n, ((1 : ℝ) - 1 / (k : ℝ) ^ 2) = ((n : ℝ) + 1) / (2 * (n : ℝ)) := by calc
        ∏ k ∈ Finset.Icc 2 n, ((1 : ℝ) - 1 / (k : ℝ) ^ 2) 
            = ∏ k ∈ Finset.Icc 2 n, ((((k : ℝ) - 1) / (k : ℝ)) * (((k : ℝ) + 1) / (k : ℝ))) := by
                apply Finset.prod_congr rfl
                intro k hk
                exact one_minus_inv_sq k (by simp_all [Finset.mem_Icc])
        _ = ((n : ℝ) + 1) / (2 * (n : ℝ)) := by
            rw [full_telescope_product n hn]
