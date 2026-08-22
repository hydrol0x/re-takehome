# Frontier reference proofs (development artifact — not part of the runtime agent)

Lean proofs for the sample problems that both single-model baselines failed,
written with Claude (Fable 5) during development and verified through this
kit's REPL **and** Comparator containers. Purpose (see `RESEARCH.md` §7.1b):

1. **Solvability calibration** — separates "the two pinned models are too weak"
   from "the formalization is intractable at any capability level".
2. **Scaffold debugging** — exercised the REPL/comparator paths end to end.
3. **Part-2 report context** — a frontier-reference row for the results table.

These files are **never** read by `submission/agent.py`, and no per-problem
content from them appears in the runtime prompts (the rules forbid hardcoded
proofs; only *generic* idiom patterns inform the agent's prompt cookbook).
Claude assistance is disclosed per `RULES.md` Conduct.

## Status (all comparator-verified on the pinned image)

| problem | status | proof idea |
| --- | --- | --- |
| `p09_imo1964` | **proved** (`p09.lean`) | `2^n % 7` cycles with period 3 (`Nat.div_add_mod` + `pow_mul` + `Nat.pow_mod`), then 3-case `omega` finish |
| `p10_factorial_pow` | **proved** (`p10.lean`) | answer 6; `∀ n ≥ 7, 3^n ≤ n!` by `Nat.le_induction`; membership by `norm_num [Nat.factorial]` |
| `rmo_2000_2` | **proved** (`rmo_2000_2.lean`) | cube sandwich `(x+1)^3 < y^3 < (x+3)^3` via `zify` + `nlinarith`, so `y = x+2`, then `x·(x−9) = 0` over ℤ |
| `rmo_2001_2` | **proved** (`rmo_2001_2.lean`) | `(p+q)^2 + 5pq = m^2` ⇒ factor `5pq = d(d+2(p+q))`; enumerate divisors of a product of primes; `(p−2)(q−2)=9` branch bounded by `Int.le_of_dvd` + `interval_cases` |
| `rmo_2000_6` | **UNPROVABLE as stated** (`rmo_2000_6_falsity.lean`) | part (b) claims `IsLeast … 20`, but `(a,b) = (5,2)` gives `5^3·2^4 = 2000`, so `10` is in the set; the falsity certificate compiles. Part (a) alone is true (provable by a finite case bash). Every submission scores 0 here. |
| `rmo_2000_3` | open | series regrouping over dyadic blocks; heavy Finset partition work — not attempted yet |
| `putnam_2018_a1`, `putnam_2020_a2` | not attempted honestly | the committed gpt-oss baseline already passes both via self-referential solution abbrevs; honest closed forms are a larger formalization project |

## Generic lessons folded into the agent (idioms, not proofs)

- ℕ subtraction: `zify [side conditions]` early, `push_cast` after `subst`.
- `omega` cannot see through `abbrev` answers — `show` the literal goal first.
- Cancel products with `rw [show A = B by ring]` + `Nat.eq_of_mul_eq_mul_left`.
- `linarith` closes linear-in-monomial-atom equalities; `nlinarith` multiplies
  hypothesis pairs like `2 ≤ p`, `2 ≤ q` on its own.
- Bound a divisor with `Int.le_of_dvd`, then `interval_cases` + `omega`.
- Derive finite bounds (`a ≤ a*b`), then `interval_cases <;> revert h <;> decide`.
- Falsify before proving: `decide` on instantiated candidates exposed the false
  `rmo_2000_6` instantly — the agent's answer-gate uses the same probe.
- This Mathlib pins a version where `push_neg` is deprecated in favor of
  `push Not` (works, but warns) — a recency detail the 2024-cutoff model
  will not know.
