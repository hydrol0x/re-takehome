import Mathlib

open Nat

/-- Divisors of a product of two primes (not necessarily distinct). -/
lemma dvd_prime_mul_prime {p q e : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (h : e ∣ p * q) : e = 1 ∨ e = p ∨ e = q ∨ e = p * q := by
  by_cases hpe : p ∣ e
  · obtain ⟨f, rfl⟩ := hpe
    have hf : f ∣ q := (mul_dvd_mul_iff_left hp.pos.ne').mp h
    rcases hq.eq_one_or_self_of_dvd f hf with rfl | rfl
    · right; left; exact mul_one p
    · right; right; right; rfl
  · have hcop : Nat.Coprime p e := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpe
    have he : e ∣ q := hcop.symm.dvd_of_dvd_mul_left h
    rcases hq.eq_one_or_self_of_dvd e he with rfl | rfl
    · left; rfl
    · right; right; left; rfl

theorem rmo_2001_2 (p q : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime q) :
  (∃ m : ℕ, p^2 + 7*p*q + q^2 = m^2) ↔
    (p = q ∨ (p = 3 ∧ q = 11) ∨ (p = 11 ∧ q = 3)) := by
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  have hpq4 : 4 ≤ p * q := Nat.mul_le_mul hp2 hq2
  constructor
  · rintro ⟨m, hm⟩
    -- (p+q)^2 + 5pq = m^2, so with d = m - (p+q) > 0:  d * (d + 2(p+q)) = 5pq
    have hsm : p + q < m := by
      by_contra hc
      push_neg at hc
      have h2 : m ^ 2 ≤ (p + q) ^ 2 := Nat.pow_le_pow_left hc 2
      nlinarith [h2, hm, hpq4]
    obtain ⟨d, hd, rfl⟩ : ∃ d, 0 < d ∧ m = (p + q) + d :=
      ⟨m - (p + q), by omega, by omega⟩
    have hkey : d * (d + 2 * (p + q)) = 5 * (p * q) := by nlinarith [hm]
    have hdvd : d ∣ 5 * (p * q) := ⟨d + 2 * (p + q), hkey.symm⟩
    have h5 : Nat.Prime 5 := by norm_num
    by_cases h5d : 5 ∣ d
    · -- d = 5e with e * (5e + 2(p+q)) = pq
      obtain ⟨e, rfl⟩ := h5d
      have hkey' : e * (5 * e + 2 * (p + q)) = p * q := by
        have h55 : 5 * (e * (5 * e + 2 * (p + q))) = 5 * (p * q) := by
          rw [← hkey]; ring
        exact Nat.eq_of_mul_eq_mul_left (by norm_num) h55
      have hedvd : e ∣ p * q := ⟨5 * e + 2 * (p + q), hkey'.symm⟩
      rcases dvd_prime_mul_prime hp hq hedvd with he | he | he | he <;> rw [he] at hkey'
      · -- 5 + 2(p+q) = pq  ==>  (p-2)(q-2) = 9  ==>  p ≤ 11, finite check
        have hpq : 5 + 2 * (p + q) = p * q := by linarith [hkey']
        have hfact : ((p : ℤ) - 2) * ((q : ℤ) - 2) = 9 := by push_cast; nlinarith [hpq]
        have hdvd9 : ((p : ℤ) - 2) ∣ 9 := ⟨(q : ℤ) - 2, hfact.symm⟩
        have hple : (p : ℤ) - 2 ≤ 9 := Int.le_of_dvd (by norm_num) hdvd9
        have hp11 : p ≤ 11 := by omega
        interval_cases p <;> omega
      · -- p * (5p + 2(p+q)) = pq  ==>  7p + q = 0, impossible
        have h1 : 5 * p + 2 * (p + q) = q :=
          Nat.eq_of_mul_eq_mul_left (by omega) hkey'
        omega
      · -- q * (5q + 2(p+q)) = pq  ==>  impossible
        rw [show p * q = q * p by ring] at hkey'
        have h1 : 5 * q + 2 * (p + q) = p :=
          Nat.eq_of_mul_eq_mul_left (by omega) hkey'
        omega
      · -- pq * (5pq + 2(p+q)) = pq  ==>  5pq + 2(p+q) = 1, impossible
        rw [show p * q = p * q * 1 from (mul_one _).symm] at hkey'
        have h1 : 5 * (p * q) + 2 * (p + q) = 1 := by
          have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < p * q)
            (by linarith [hkey'] : (p * q) * (5 * (p * q) + 2 * (p + q)) = (p * q) * 1)
          linarith [this]
        linarith [hpq4, h1]
    · -- d coprime to 5, so d ∣ pq
      have hcop : Nat.Coprime 5 d := (Nat.Prime.coprime_iff_not_dvd h5).mpr h5d
      have hdpq : d ∣ p * q := hcop.symm.dvd_of_dvd_mul_left hdvd
      rcases dvd_prime_mul_prime hp hq hdpq with he | he | he | he <;> rw [he] at hkey
      · -- 1 + 2(p+q) = 5pq, impossible for primes ≥ 2
        have h1 : 1 + 2 * (p + q) = 5 * (p * q) := by linarith [hkey]
        nlinarith [h1, hp2, hq2]
      · -- p + 2(p+q) = 5q  ==>  3p = 3q
        rw [show 5 * (p * q) = p * (5 * q) by ring] at hkey
        have h1 : p + 2 * (p + q) = 5 * q :=
          Nat.eq_of_mul_eq_mul_left (by omega) hkey
        omega
      · -- q + 2(p+q) = 5p  ==>  p = q
        rw [show 5 * (p * q) = q * (5 * p) by ring] at hkey
        have h1 : q + 2 * (p + q) = 5 * p :=
          Nat.eq_of_mul_eq_mul_left (by omega) hkey
        omega
      · -- pq + 2(p+q) = 5, impossible
        rw [show 5 * (p * q) = p * q * 5 by ring] at hkey
        have h1 : p * q + 2 * (p + q) = 5 :=
          Nat.eq_of_mul_eq_mul_left (by omega) hkey
        linarith [hpq4, h1]
  · rintro (rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨3 * p, by ring⟩
    · exact ⟨19, by norm_num⟩
    · exact ⟨19, by norm_num⟩
