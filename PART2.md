# Part Two — Does two-model collaboration beat either model alone?

**Short answer: yes, by a small but repeatable margin at matched budgets —
and the reason is portfolio coverage plus a verifier-gated division of
labor, not conversational synergy.** The compiler is the only judge that
matters; the second model earns its place where it adds *coverage* (different
failure modes) or *independent confirmation of compact decisions* (numeric
answers), and nowhere else we could measure.

Evidence base: matched 30-minute-cap arms (two seeds), hard-tier runs at
1–2 h caps, and a completed full-cap validation run at exact judge
settings (8 h / $1.00 per problem) — see §2b and `EXPERIMENTS.md`.

## 1. Experimental design

Three arms share **the same code path**; a `SUBMISSION_MODELS` switch
selects which models the ladder may call (`duo`, solo `qwen`, solo
`gptoss`). Everything else — deterministic tactic sweep, sampling loop,
repair, decomposition, time/budget management — is identical, so
differences measure the model portfolio, not harness luck. Each arm ran the
full 16-problem sample set at `VM_TIME_LIMIT_S=1800`, twice (independent
seeds/days). The kit's built-in single-model 25-turn baseline loops provide
a floor. The scorable ceiling is **14/16**: `rmo_2000_6` part (b) is
mathematically false as stated and `rmo_2000_3`'s pristine challenge fails
the comparator build (details and disproof in `reference/`).

## 2. Results (matched 30-minute caps)

| arm | seed 1 | seed 2 | spend (s1 / s2) |
| --- | --- | --- | --- |
| **duo (coordination layer)** | **9/16** | **10/16** | $0.16 / $0.17 |
| solo qwen3.5-flash | 8/16 | 9/16 | $0.45 / $0.40 |
| solo gpt-oss-120b | 8/16 | 9/16 | $0.04 / $0.01 |
| kit baseline, qwen | 7/16 | — | — |
| kit baseline, gpt-oss | 8/16 | — | — |

- The duo beat the best solo arm by **+1 on both seeds**, at one-half to
  one-third of solo-qwen's cost.
- Seed-1 duo exactly equaled the **union** of the two solo arms: the solos
  fail *different* problems (qwen missed both Putnams; gpt-oss missed
  `p07_least_divisible`).
- Across all six arm runs, 11 distinct problems were solved at short caps;
  the hard tier (`p09`, `p10`, `rmo_2000_2`, `rmo_2001_2`) additionally
  yielded `p10_factorial_pow` at longer caps (§4).

## 2b. Full-cap validation (exact judge settings)

One duo run of the four hard problems at `VM_TIME_LIMIT_S=28800`
`VM_BUDGET_USD=1.00` (run `20260823T230042Z`): **2/4, both first-ever
solves for the model pair**.

| problem | outcome | spend | wall |
| --- | --- | --- | --- |
| p09_imo1964 | **comparator PASS** | $0.098 | 115 min |
| rmo_2000_2 | **comparator PASS** | $0.748 | 444 min |
| p10_factorial_pow | REPL-accepted; comparator timed out (180 s) | $0.211 | 105 min |
| rmo_2001_2 | honest incomplete (2 subgoals never closed) | $0.805 | 460 min |

Two findings matter for the collaboration question. First, **p09's winning
skeleton came from gpt-oss** in the sketcher alternation (qwen sketches
first; gpt-oss's round produced the decomposition whose holes filled) — at
full caps, cross-model sketch diversity contributed a solve a solo-qwen arm
would not have had. Second, rmo_2000_2 needed 7.4 hours and three quarters
of the dollar cap: the hard tier is a capability×time problem, and
short-cap arm scores understate what the identical system does with the
judged window. Cumulatively the pair has comparator-passed 3 of the 4
provable hard problems (p10 passed at 2 h and 30 min caps in other runs);
only rmo_2001_2 has never closed.

## 3. Where the duo's edge actually comes from

Mechanism attribution, in decreasing order of measured value:

1. **Free floor (not a collaboration effect).** The deterministic tactic
   sweep (S0) solves 6/16 at zero LLM cost in every arm. Any honest
   comparison must subtract it; claims of "collaboration" that include the
   sweep would be theater.
2. **Cross-model answer consensus (S0.5) — genuine effect #1.** For
   answer-then-prove problems, both models independently derive the numeric
   answer; agreement pins it as a literal, after which `decide`-class
   tactics often finish free. This converted `p06_pow_mod` and
   `p07_least_divisible` for ~$0.005 total. The control: solo gpt-oss
   *agreed with itself* on a wrong path for p07 and lost the problem. A
   wrong pinned answer poisons the entire downstream search and the
   verifier cannot reject it quickly — this is precisely the compact,
   high-leverage decision where independent-family agreement pays
   (RESEARCH.md §6.1).
3. **Portfolio sampling (S1) — genuine effect #2.** The two model families
   fail differently (qwen: Putnam-style algebra; gpt-oss: the p07 answer
   trap). Pooled diverse sampling with the compiler as filter buys the
   union of their coverage — consistent with cross-family union-coverage
   results in the literature (arXiv 2510.21513) and with
   repeated-sampling-under-a-verifier scaling (arXiv 2407.21787).
4. **Cascade cost discipline.** gpt-oss engages only where the cheaper
   qwen wave and the sweep have already failed, so the duo is *cheaper*
   than solo-qwen while scoring higher. Model participation on solved
   problems reflects need, not quota (`models_used` in `result.json`).
5. **Sketch/fill decomposition (S4) — depth is the engine, cross-model
   sketch diversity is a real second-order term.** The first hard-tier
   solve (`p10_factorial_pow`, comparator-PASS at 2 h caps, $0.0497) came
   from a qwen sketch → skeleton repair → depth-first hole fills, and
   solo-qwen reproduced p10 at a 30-minute cap — so the fill *loop*
   (best-failure seeding, sorrify salvage, lemma harvesting) is the
   driver and works within one family. But at full caps the alternation
   itself scored: p09's winning skeleton was gpt-oss's (§2b), a
   decomposition the qwen-only arm would never have proposed. Depth does
   the proving; having two sketchers widens which decompositions exist to
   be deepened.

## 4. What collaboration costs

The duo's one measured cost is **exposure to the gpt-oss channel**, whose
cheap provider tier produced every ledger-closing failure across all runs
(429 bursts, 502s, truncated bodies); duo seed-2 lost its p10 attempt to
one such death while solo-qwen solved it. Solo-qwen arms have lost zero
ledgers ever. Mitigations now in the tree: the maintainer-approved kit
fixes mirrored into `src/re_harness/llm.py` (provider fallbacks under the
price ceiling; HTTP refusals release instead of closing the ledger), plus
agent-side ordering (bank qwen's work before the first risky call),
serialization, and per-problem call caps.

A second cost surfaced at full caps, orthogonal to collaboration: REPL
acceptance does not screen **kernel cost**, and one REPL-valid p10 proof
timed out the comparator's cold 180 s build. The agent now measures each
check's wall time and defers any accepted proof needing >40 s in the warm
REPL — held as fallback while it hunts a lighter proof whenever ≥30 min
of window remain.

## 5. What we looked for and did not find

- **Debate / free-form mutual critique:** rejected at design time on the
  literature (arXiv 2310.01798, 2502.08788: verdict flips under pressure,
  no reliable error localization) and never missed in practice — compiler
  error messages are strictly better critique than a second model's
  opinion.
- **Answer arbitration beyond compact decisions:** consensus on whole
  proofs is worthless because the verifier already adjudicates proofs for
  free; consensus only pays where verification is *slow* (a wrong pinned
  answer can burn the whole window).
- **Model-role folklore:** neither model is a universally better sketcher
  or filler. gpt-oss-high sketched the decompositions that led to early
  hard-tier progress, but its sketch calls also produced the ledger
  deaths; qwen-led sketching produced the actual p10 solve. Roles earned
  by measurement, not by press release.

## 6. Frontier reference

As an upper-bound reference, a frontier assistant (Claude, disclosed per
the rules) hand-proved all four provable hard-tier problems and certified
the 14/16 ceiling (`reference/`: comparator-verified `p09`, `p10`,
`rmo_2000_2`, `rmo_2001_2`, the `rmo_2000_6` disproof, and the
`rmo_2000_3` build diagnosis). The gap between the pair-at-caps and the
ceiling is concentrated in multi-lemma decomposition depth — exactly the
stage that needs the full 8-hour window.

## 7. Caveats

- Two seeds, ±1 seed-to-seed variance per arm: the +1 duo edge is
  consistent but small; the cost advantage (2–3× under solo-qwen) is
  large and stable.
- All numbers are from a web dev container with documented environmental
  hazards (restart storms, an egress proxy) — see `EXPERIMENTS.md` and
  `RUNBOOK.md`; provider-health effects may differ at judging time.
- The full-cap validation is a single run (n=1) of the hard tier in the
  duo arm only; matched solo arms at full caps were not run (8 h × 4
  problems × 3 arms exceeds the dev window). The duo-vs-solo comparison
  rests on the matched short-cap arms; the full-cap run shows what the
  chosen system does at judged settings.

## 8. Post-arm development: the selection loop and the verifier's last word

After the arm experiments, a two-day variant-selection loop ran on a
**custom 24-problem eval set** (authored in kit format with
machine-verified reference proofs; 16-problem dev split for selection, 8
held back for overfitting checks — `RESEARCH_LOOP.md`). Outcomes that
bear on the collaboration question:

- **Two promotions** (window-proportional time constants; breadth-first
  hole filling) lifted the dev set from 11/16 to 13/16 and held on the
  held-back set (6/8 twice). Both are identity-or-benign at judge caps.
- **The comparator precheck** — the loop's most valuable product — came
  from chasing a failure the REPL cannot see: three p10 proofs were
  REPL-accepted yet timed out the comparator's cold build. The agent now
  verifies accepted winners against the *actual* comparator when time
  permits, demoting timeouts to fallback and continuing the hunt. Live
  results: p09 re-passed at judge caps after the precheck rejected two
  would-be-fatal proofs (the run ships 0/4 without it), and p10 finally
  converted ($0.029, 38 min) after three straight timeout losses. This is
  the verifier-centric thesis at its endpoint: when the scoring gate and
  the search-time checker disagree, trust only the gate.
- **Negative results kept**: deeper fill reasoning (12/16, no structural
  gain, +16 % cost) and gpt-oss inside short-window sampling waves
  (halves qwen's cycle count) were measured and rejected; mined cascade
  tactics were kept on direct archived-hole evidence but showed no live
  win. Selection was by composition, not raw totals — per-problem seed
  noise at short caps is ±2.

## Verdict

At matched budgets the coordination layer was never worse than the best
solo arm, beat it by one problem on both seeds, matched the union of the
solos, and cost a fraction of the stronger solo. At exact judge settings
it closed two hard problems the pair had never solved — one from a
gpt-oss skeleton the solo arm could not have produced, one after 7.4
hours of accumulated lemma-building. The mechanism is unglamorous and
robust: **let a compiler judge, buy coverage from two model families,
spend consensus only on compact decisions, and escalate depth (not
chatter) on hard problems.**
