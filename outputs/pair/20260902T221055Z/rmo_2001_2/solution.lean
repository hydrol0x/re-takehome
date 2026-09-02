import Mathlib

open Nat

theorem rmo_2001_2 (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
  (∃ m : ℕ, p^2 + 7*p*q + q^2 = m^2) ↔
    (p = q ∨ (p = 3 ∧ q = 11) ∨ (p = 11 ∧ q = 3)) := by
  constructor
  · -- Forward direction
    intro h
    rcases h with ⟨m, hm⟩
    have h_m_gt : m > p + q := by
      -- Prove m > p + q
      have h_sq : (p + q)^2 < m^2 := by
        calc
          (p + q)^2 = p^2 + 2*p*q + q^2 := by ring
          _ < p^2 + 7*p*q + q^2 := by
            have h_pos : 0 < 5*p*q := by
              apply mul_pos
              · exact Nat.Prime.pos hp
              · exact Nat.Prime.pos hq
            nlinarith [h_pos]
          _ = m^2 := by rw [hm]
      exact Nat.lt_of_le_of_lt (by nlinarith) h_sq
    have h_diff : (m - (p + q)) * (m + (p + q)) = 5 * p * q := by
      calc
        (m - (p + q)) * (m + (p + q)) = m^2 - (p + q)^2 := by
          have h_sub : p + q ≤ m := by linarith
          rw [Nat.mul_sub_left_distrib, Nat.mul_sub_right_distrib]
          simp [Nat.add_sub_cancel_left, Nat.add_sub_cancel_right, Nat.mul_add, Nat.add_mul]
          <;> ring_nf at * <;> omega
        _ = (p^2 + 7*p*q + q^2) - (p^2 + 2*p*q + q^2) := by rw [hm]
        _ = 5 * p * q := by ring
    set d₁ := m - (p + q) with hd₁
    set d₂ := m + (p + q) with hd₂
    have h_prod : d₁ * d₂ = 5 * p * q := by rw [hd₁, hd₂]; exact h_diff
    have h_sum : d₂ - d₁ = 2 * (p + q) := by
      rw [hd₁, hd₂]
      have h_sub : p + q ≤ m := by linarith
      simp [Nat.add_sub_cancel_left, Nat.add_sub_cancel_right]
      <;> ring_nf
      <;> omega
    have h_d₁_pos : d₁ > 0 := by
      rw [hd₁]
      linarith
    have h_d₁_dvd : d₁ ∣ 5 * p * q := by
      use d₂
      rw [hd₁, hd₂]
      exact h_prod
    -- Now we need to iterate through divisors of 5pq
    -- Since p, q are primes, divisors are 1, 5, p, q, 5p, 5q, pq, 5pq
    -- We need to handle the case where p=q and p≠q separately potentially
    -- Or just analyze d₁ directly.
    
    -- To make it easier, let's consider cases on whether p=q
    by_cases h_eq : p = q
    · -- Case p = q
      -- If p = q, then p^2 + 7p^2 + p^2 = 9p^2 = (3p)^2, so m = 3p works.
      -- We need to show this is consistent with the RHS of the iff.
      -- The RHS includes p=q, so this direction holds trivially.
      -- Wait, the goal is to show (exists m ...) -> (p=q or ...).
      -- If p=q, then the RHS is true. So we just need to finish the proof.
      exact Or.inl h_eq
    · -- Case p ≠ q
      -- Without loss of generality assume p < q or something?
      -- Actually, the divisors depend on p and q.
      -- Since p, q are distinct primes, 5pq has divisors 1, 5, p, q, 5p, 5q, pq, 5pq.
      -- We know d₁ * d₂ = 5pq and d₂ - d₁ = 2(p+q).
      -- Also d₁ < d₂ because 2(p+q) > 0.
      -- So d₁ < sqrt(5pq).
      
      -- We can try to bound d₁.
      -- d₁(d₁ + 2(p+q)) = 5pq
      -- d₁^2 + 2(p+q)d₁ - 5pq = 0
      
      -- Let's enumerate possible values for d₁.
      -- d₁ must divide 5pq.
      -- Since p, q are primes, the divisors are limited.
      -- However, proving d₁ is one of these requires knowing p, q are primes.
      -- We can use `Nat.Prime.dvd_mul` etc.
      
      -- A cleaner way might be to use the fact that d₁ | 5pq.
      -- Since p, q are primes, any divisor d of 5pq is of form 5^a * p^b * q^c where a,b,c in {0,1}.
      -- But we need to be careful about ordering.
      
      -- Let's try to derive a contradiction for most cases.
      -- We have d₁ * d₂ = 5pq.
      -- d₂ = d₁ + 2(p+q).
      -- d₁(d₁ + 2(p+q)) = 5pq.
      
      -- Consider d₁ = 1.
      -- 1(1 + 2(p+q)) = 5pq => 1 + 2p + 2q = 5pq.
      -- 5pq - 2p - 2q = 1.
      -- Multiply by 5: 25pq - 10p - 10q = 5.
      -- (5p - 2)(5q - 2) = 9.
      -- Since p, q >= 2, 5p - 2 >= 8.
      -- Product >= 64 > 9. Contradiction.
      
      -- Consider d₁ = 5.
      -- 5(5 + 2(p+q)) = 5pq => 5 + 2p + 2q = pq.
      -- pq - 2p - 2q = 5.
      -- (p-2)(q-2) = 9.
      -- Factors of 9: 1*9, 3*3, 9*1.
      -- p-2=1 => p=3. q-2=9 => q=11. (3, 11)
      -- p-2=3 => p=5. q-2=3 => q=5. (5, 5) but p!=q here.
      -- p-2=9 => p=11. q-2=1 => q=3. (11, 3)
      
      -- Consider d₁ = p.
      -- p(p + 2(p+q)) = 5pq => p + 2p + 2q = 5q => 3p = 3q => p=q. Contradiction.
      
      -- Consider d₁ = q.
      -- Similar to above, leads to p=q.
      
      -- Consider d₁ = 5p.
      -- 5p(5p + 2(p+q)) = 5pq => 5p + 2p + 2q = q => 7p + q = 0. Impossible.
      
      -- Consider d₁ = 5q.
      -- Similar, impossible.
      
      -- Consider d₁ = pq.
      -- pq(pq + 2(p+q)) = 5pq => pq + 2p + 2q = 5.
      -- Since p, q >= 2, pq >= 4.
      -- If p=2, q=2, pq=4. 4 + 4 + 4 = 12 != 5.
      -- If p=2, q=3, pq=6. 6 + 4 + 6 = 16 != 5.
      -- Generally pq + 2p + 2q > 5 for primes p, q.
      
      -- So only d₁ = 5 works, giving (3, 11) or (11, 3).
      
      -- We need to formalize "d₁ divides 5pq" and "d₁ is one of...".
      -- Since p, q are primes, we can use `Nat.Prime.dvd_mul`.
      -- d₁ | 5 * p * q.
      -- Since 5 is prime, p is prime, q is prime.
      -- Any divisor d of 5pq is of form 5^i * p^j * q^k.
      -- But we need to be careful if p=5 or q=5.
      -- If p=5, then 5pq = 25q. Divisors are different.
      -- So we should split into cases: p=5, q=5, neither is 5.
      
      -- Actually, simpler approach:
      -- Just check all divisors of 5pq.
      -- But listing them depends on equality of p, q, 5.
      -- Maybe just use `Nat.le_of_dvd` and bounds?
      -- d₁ < sqrt(5pq).
      -- And d₁ | 5pq.
      
      -- Let's try to construct the proof using `have` statements and case splits.
      -- We need to import `Mathlib.Tactic.Ring` for `ring`.
      -- We need `Mathlib.Data.Nat.Prime.Basic` for prime properties.
      
      sorry
  · -- Backward direction
    intro h
    rcases h with (h_eq | ⟨h_p, h_q⟩ | ⟨h_p, h_q⟩)
    · -- p = q
      use 3 * p
      rw [h_eq]
      ring
    · -- p = 3, q = 11
      use 15
      rw [h_p, h_q]
      norm_num
    · -- p = 11, q = 3
      use 15
      rw [h_p, h_q]
      norm_num
