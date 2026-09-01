have h_u_val : u = 2 := by
      have h_u_in : u ∈ ({1, 2, 3} : Set ℕ) := by
        interval_cases u <;> simp_all [Set.mem_insert, Set.mem_singleton_iff]
        <;> try omega
        <;> try {
          have : ¬ u ∣ 16 := by
            norm_num
            simp_all [Nat.dvd_iff_mod_eq_zero]
          contradiction
        }
      rcases h_u_in with (rfl | rfl | rfl)
      · -- u = 1
        ...
      · -- u = 2
        exact rfl
      · -- u = 3
        ...
