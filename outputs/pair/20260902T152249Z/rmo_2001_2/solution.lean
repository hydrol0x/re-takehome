theorem rmo_2001_2 (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
  (∃ m : ℕ, p^2 + 7*p*q + q^2 = m^2) ↔
    (p = q ∨ (p = 3 ∧ q = 11) ∨ (p = 11 ∧ q = 3)) := by
  constructor
  · intro h
    rcases h with ⟨m, hm⟩
    -- Prove forward direction
  · intro h
    rcases h with (h | h | h)
    · -- Case p = q
    · -- Case p = 3, q = 11
    · -- Case p = 11, q = 3
