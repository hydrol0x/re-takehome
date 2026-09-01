import Mathlib

/-- If `x` and `y` are positive reals with `x + y = 1`, then
`(1 + 1/x) * (1 + 1/y) ≥ 9`. -/
theorem m03_recip9 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (h : x + y = 1) :
    9 ≤ (1 + 1 / x) * (1 + 1 / y) := by
  have hxy : x * y ≤ 1 / 4 := by
    have h1 : 0 < x * y := mul_pos hx hy
    have h2 : (x - y)^2 ≥ 0 := sq_nonneg _
    nlinarith
  
  have hmain : 9 ≤ (1 + 1 / x) * (1 + 1 / y) := by
    have hpos_x : 0 < x := hx
    have hpos_y : 0 < y := hy
    have hpos_xy : 0 < x * y := mul_pos hx hy
    
    -- Expand the product and simplify
    calc
      (1 + 1 / x) * (1 + 1 / y) 
        = 1 + 1 / x + 1 / y + 1 / (x * y) := by
          field_simp [hpos_x.ne', hpos_y.ne']
          ring
      _ = 1 + (x + y) / (x * y) + 1 / (x * y) := by
          field_simp [hpos_xy.ne']
          ring
      _ = 1 + 1 / (x * y) + 1 / (x * y) := by rw [h]
      _ = 1 + 2 / (x * y) := by ring
      _ ≥ 1 + 2 / (1 / 4) := by
          gcongr
          <;> linarith
      _ = 9 := by norm_num
  
  exact hmain
