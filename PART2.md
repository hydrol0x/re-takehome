# Part Two — Does two-model collaboration beat either model alone?

**Short answer: yes, by a small but repeatable margin at matched budgets —
and the reason is portfolio coverage plus a verifier-gated division of
labor, not conversational synergy.** The compiler is the only judge that
matters; the second model earns its place where it adds *coverage* (different
failure modes) or *independent confirmation of compact decisions* (numeric
answers), and nowhere else we could measure.

Status note: numbers below are from matched 30-minute-cap arms (two seeds)
plus hard-tier runs at 1–2 h caps. A full-cap (8 h / $1.00, judge-setting)
validation run is in flight; its results will be appended to
`EXPERIMENTS.md` and folded in here.

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
5. **Sketch/fill decomposition (S4) — value is depth, not dialogue.** The
   hard-tier solve (`p10_factorial_pow`, comparator-PASS at 2 h caps,
   $0.0497) came from a qwen sketch → skeleton repair → depth-first hole
   fills. Solo-qwen seed-2 then reproduced p10 at a 30-minute cap. So the
   fill *loop* (best-failure seeding, sorrify salvage, lemma harvesting)
   is the driver, and it works within one family; the duo's S4 role is
   alternation after plateaus, an insurance policy rather than the engine.

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
- The 30-minute arms understate every arm's absolute ability (the judged
  setting is 8 h); the full-cap validation run addresses this.

## Verdict

At matched budgets the coordination layer was never worse than the best
solo arm, beat it by one problem on both seeds, matched the union of the
solos, and cost a fraction of the stronger solo. The mechanism is
unglamorous and robust: **let a compiler judge, buy coverage from two
model families, spend consensus only on compact decisions, and escalate
depth (not chatter) on hard problems.**
