# Research loop — variant selection on the custom eval set

Goal: use the remaining key budget (~$46) and days before the deadline to
improve the coordination agent measurably, with selection pressure from a
wider problem distribution than the 16 kit samples.

## Eval sets

- `custom-problems-dev/` — 16 problems (easy/answer/medium/hard mix),
  authored by frontier-assistant subagents in exact kit format, each with a
  REPL-verified reference proof (truth certificate) and a
  comparator-build-verified pristine challenge. **Selection metric runs
  here.** Reference proofs live in `reference-custom/` and are never read
  by the agent (same policy as `reference/`).
- `custom-problems-held/` — 8 problems held back from the loop. Run rarely
  (promotion candidates only) to detect overfitting to the dev set.
- Composition (all 24 authored 2026-08-25; every reference proof
  independently re-verified, comparator spot-passes on all easy+hard pairs
  at 59–77 s builds): dev = c01_quad_roots, c02_amgm_frac,
  c03_coprime_linear, c05_pow_sum_div, c06_three_pow, c08_count_congr,
  c10_tau_360, m01_dvd13, m02_ord25, m04_sumfact, m06_factcop, m08_amgm8,
  h01_legendre100, h02_mod23_cycle, h04_square_shift, h05_telescope_prod;
  held = c04_sum_odds, c07_order_three, c09_factorial_mod, m03_recip9,
  m05_divbash, m07_sumgeo, h03_invsq_sum, h06_order_mod125.
- The 16 kit samples remain the reporting benchmark; the loop never
  selects on them directly (they are closer to the holdout's format
  quirks and we do not want to tune to their two broken entries).

## Metric

One eval = `PYTHONPATH=scripts/devshim VM_TIME_LIMIT_S=1200
VM_BUDGET_USD=1.00 VM_TRANSPORT_FAILURE_POLICY=release
SUBMISSION_MODELS=duo <variant env> .venv/bin/python run.py --problems
custom-problems-dev --out outputs --n-workers 4` (~80–100 min, ~$0.2–0.5).

Ranking: (1) problems solved (comparator-passed); (2) fewer ledger deaths
(any `cost_unknown` under judge-default policy disqualifies); (3) lower
spend; (4) lower wall-clock. 20-minute caps keep evals cheap and still
separate variants on the easy/medium tiers; periodic long-cap runs on the
hard tier sanity-check that short-cap selection transfers.

## Variant mechanics

- Variants are env-flag-selectable behaviors in `submission/agent.py`
  (`SUBMISSION_*` knobs; new behaviors land behind flags with the current
  behavior as default). One branch, no forks; judging runs whatever the
  promoted defaults are.
- Each iteration: analyze the latest eval's failures (transcripts +
  events) → pick 2–3 hypotheses → implement → eval each (sequential, the
  container fits one 4-worker run) → promote the winner by flipping its
  flag default → log here → next iteration.
- Held-back set runs only when a promotion happens; a promotion that wins
  dev but regresses held is reverted (overfitting signal).

## Candidate backlog (from accumulated failure analysis)

- V1 `qwen-think` reasoning budget 12k → 20k on S4 fills (hard-tier holes
  die on truncated reasoning more than wrong ideas).
- V2 S1 wave mix: shift samples from qwen-fast to qwen-think as caps grow.
- V3 Sketch granularity: push DSP+ "many small lemmas" harder in the
  sketch prompt; reject skeletons whose holes exceed a size bound.
- V4 Fill budget: sequential repair dialogues per hole 3 → 5 with the
  saved time from V3's smaller holes.
- V5 S0 sweep additions: gcongr-chain, zify+omega, and
  bound-derivation+interval_cases+decide composite entries (idioms that
  won repeatedly in reference proofs).
- V6 gpt-oss S1 wave at cycle 1 again (refusals are survivable post-fix;
  deferral may now cost coverage).
- V7 Comparator-cost guard threshold tuning (40 s default; measure).
- V8 Re-sketch diversity: vary sketcher temperature/plan framing per round
  instead of fixed.

## Log

| iter | date | variants tested | dev score (base → best) | promoted | notes |
| --- | --- | --- | --- | --- | --- |
| 0 | 2026-08-25 | baseline v6+guard | **11/16** ($0.136, 19 min, run `20260825T161057Z`) | — | easy 7/7, medium 3/5, hard 1/4; zero ledger deaths |
| 1 | 2026-08-25 | `SUBMISSION_SHORTCAP` (window-proportional constants) | 11 → **9/16** ($0.124, 33 min, `20260825T163350Z`) | no — regression | mechanics worked (gpt-oss usable 2/2, S4 engaged, c03 one hole short) but slow serialized gpt-oss S1 calls halved qwen's cycle count: lost c03+m01, regained h05 |
| 2 | 2026-08-25 | shortcap + skip gpt-oss S1 wave at short windows (`c518381`) | 11 → **10/16** ($0.114, 37 min, `20260825T170727Z`) | **yes — default on** | first-ever m04 solve (S4 at short caps — the baseline structurally could not), m01 recovered; c03/h05 lost to S1 seed-noise (both flip across runs). Totals 11/9/10 are within noise; promoted on composition + mechanism + judge-cap safety (identity ≥ 40-min windows) |

Held-set validation of the promotion (run `20260825T174536Z`): **6/8**
($0.097) — c04, c07, c09, m03, m07, and hard-tier h06 (order of 2 mod
125); missed h03 (inverse-square induction) and m05 (divisibility bash).
Held rate 75% ≥ dev 62%: no overfitting signal, promotion stands.

| 3 | 2026-08-25 | `SUBMISSION_FILL_BREADTH` (cascade all holes first; window-scaled dialogues) | 10 → **13/16** ($0.155, 28 min, `20260825T180137Z`) | **yes — default on** | +2 over best-ever with structural gain: h01 closed (first time), all three flippers (c03, m01, h05) held simultaneously, m04 repeated. Remaining: h02, h04, m06 (full windows, fills fail on the real math) |

| 6 | 2026-08-26 | mined FILL_SWEEP entries (pow-normalization, pow-mod, sq_sub_sq) | 13 → 11/16 ($0.257, 43 min, `20260826T080252Z`) | kept (already default) | delta = flippers c03/m01 exactly; h01/m04/h05 held; no live structural win this seed — entries stand on their archived-hole evidence, cost bounded to cascade seconds |
| 7 | 2026-08-26 | `SUBMISSION_SKELETON_KEEP` (resume best partial skeleton) | 13 → 12/16 ($0.185, 45 min, `20260826T084608Z`) | no — stays opt-in | within noise (flippers c03/m01 in, h05 out; structural three unmoved). Its regime is long windows (cross-cycle/restart continuity) — short-cap evals cannot show it; left available for full-cap use |
| 4 | 2026-08-25 | `SUBMISSION_FILL_REASONING` (16k-thought fills) | 13 → 12/16 ($0.180, 33 min, `20260825T184602Z`) | no | within noise (delta = flipper m01); no structural gain — h02/h04/m06 resist deeper thinks at short caps; costs +16%. The structural three likely need window, not thought budget |

Held-set validation of the fill-breadth promotion (`20260825T183009Z`):
**6/8** — identical composition to the shortcap check (h03 and m05 are
the held set's own structural pair). Promotion stands.

Transfer check, kit sample-16 at 30-min caps with the promoted config
(`20260825T192220Z`): **9/16**, $0.341, zero ledger deaths — within the
duo arm's historical 9–10 band, not an improvement. Honest read: the
custom-set gains come from problems whose decompositions fit a short
window (the set was authored that way); the kit's hard tier needs hours
regardless (full-cap runs prove it), so at 30-min caps the promoted
config neither helps nor hurts the kit set. At judge caps the promotions
are identity (shortcap) or cheap-positive (breadth pass).

Transfer check, kit hard4 at 60-min caps with the promoted config
(`20260825T200925Z`): **0/4**, $0.150 — same total as the v3 agent's
60-min attempt, but with a structural near-miss: p10 reached a
REPL-accepted proof in 21.5 min (v5 needed 64 min at 2 h caps) and lost
only to the comparator-timeout class; the 15 s guard (pushed after this
run started) targets exactly that. p09/rmo_2000_2/rmo_2001_2 used full
~44-min windows: the kit hard tier needs hours, consistent with full-cap
evidence.

Full-cap re-validation with promoted config + precheck
(`20260825T205403Z`): 1/4 — p09 PASS with the **comparator precheck
saving the point live** (two REPL-accepted proofs rejected on real-gate
timeouts before a 52 s-build proof shipped); rmo_2000_2 regressed to
incomplete across a restart-split window; details in EXPERIMENTS.md.

Tactic mining vs archived failed holes (subagent, Lean-only,
2026-08-26): corpus 57 sorried files / 209 holes inventoried, 6 files /
27 holes measured under host caps. Three additions won holes nothing in
FILL_SWEEP closed — a pow-normalization+omega combo (m01 induction
step), a pow-mod simp set (p09 mod-cycle family), and `Nat.sq_sub_sq`
(h04 difference-of-squares); 13 other candidates closed nothing. Also
measured: 17/27 holes resist every generic tactic (fills need real
proofs), and existing entries omega/nlinarith dominate the closable
remainder. Additions landed in FILL_SWEEP as iter-6; eval queued behind
the p10 precheck-validation run.

p10 precheck validation (`20260826T062410Z`, 2 h cap, 1 worker):
**comparator PASS, 1/1** ($0.029, 38 min, gpt-oss S1 sample) — the
winning proof cleared the precheck (97 s) and the final comparator
(45 s). After three straight comparator-timeout losses on p10, the
precheck-equipped stack ships a verified point. The comparator-timeout
class is now handled end-to-end: reject-heavy-and-keep-hunting at S5,
confirmed live on both p09 (reject path) and p10 (accept path).

## Phase 2 — parallel research branches (2026-08-26 →)

Up to a dozen independent branches, architecture: **fan-out
implementation** (worktree subagents, one flag each, offline tests,
patch review) → **serialized eval funnel** (the box fits one 4-worker
eval; ~45 min and ~$0.3 per slot) → promotion by composition with
held-set checks, unchanged. All flags default off until promoted.

| branch | flag | method | targets |
| --- | --- | --- | --- |
| B1 | `SUBMISSION_WAVE_SPREAD` | temperature spread (0.5/0.8/1.1) across the qwen-fast wave, +2 samples at short caps | flipper variance (c03/m01/h05) |
| B2 | `SUBMISSION_PLAN_FIRST` | sample 3 short informal plans, majority-pick strategy, condition proof samples on it (DSP-lite for whole proofs) | wrong-strategy waves |
| B3 | `SUBMISSION_CLUSTER_REPAIR` | cluster S2 near-misses by error signature; repair the representative; apply the winning fix pattern to siblings | repair efficiency |
| B4 | `SUBMISSION_TYPED_FILLS` | classify hole goals syntactically (arith/induction/divisibility/inequality/cast) → class-specialized fill prompts | fill quality |
| B5 | `SUBMISSION_PREMISE_HINTS` | model proposes Mathlib lemma names for the statement; batch-verify existence via REPL `#check`; inject only verified names into fill prompts | name-hallucination fill errors |
| B6 | `SUBMISSION_SUGGEST_HARVEST` | run `exact?`/`apply?` on stuck holes, harvest "Try this:" suggestions into fill prompts (per-hole; S0 only had whole-file) | stuck holes |
| B7 | `SUBMISSION_STRENGTHEN_IH` | after two failed induction-hole fills, re-sketch note explicitly asks to strengthen the induction hypothesis | m01/h03-class inductions |
| B8 | `SUBMISSION_CRITIC_NOTES` | on S2 plateau, gpt-oss-high writes a bounded diagnosis note (not a proof) injected into the next wave's history | cross-model critique, bounded |
| B9 | `SUBMISSION_SKELETON_PORTFOLIO` | keep the 2 best distinct skeletons; alternate fill effort between them | wrong-first-skeleton (h02/h04) |
| B10 | `SUBMISSION_BOUND_TEMPLATES` | deterministic templates: derive bounds for bounded-quantifier goals → `interval_cases`/`decide` reformulations in the per-hole cascade | bounded goals, zero LLM cost |
| B12 | (eval-only) | skeleton-keep + tuned knobs at 60-min caps on kit hard4 | long-window transfer |

Phase-2 eval results:

| branch | dev score | verdict |
| --- | --- | --- |
| B1 wave-spread | 9/16 ($0.230, `20260826T144557Z`) | no — c03 recovered but c02 (an always-pass easy) and h01 flipped fail; spread dilutes the productive t=0.8 mass |
| B5 premise-hints | **13/16** ($0.206, `20260826T153552Z`) | promotion candidate — ties best-ever; first eval to hold ALL flippers (c03/m01/h05) simultaneously + h01 + m04; second seed queued |
| B6 suggest-harvest | 11/16 ($0.196, `20260826T161532Z`) | no — lost both flippers c03/h05 and all three structurals h02/h04/m06. Probe telemetry: harvest fired hardest exactly on the failures (m06 19 Try-this, h05 12, c03 5) without converting any, and c05/h04 spent 12–14 probes for zero suggestions — `apply?` surfaces term-mode lemma applications that don't close these goals, while the probe checks crowd out productive fill rounds |

Eval order by expected value: B5, B6, B1, B2, B9, B10, B3, B4, B7, B8;
then second seeds for the top three, a combination eval of compatible
winners, held-set on any promotion, and B12.

**Loop close-out (2026-08-26).** Seven iterations, ~$1.6 of eval spend.
Final configuration: shortcap + fill-breadth promoted defaults, mined
cascade entries, comparator precheck default-on; fill-reasoning and
skeleton-keep available as opt-in flags. Dev-set trajectory 11 → 13 with
±2 seed noise; held set stable at 6/8 throughout; the precheck — the
loop's chief product — is validated live in both directions (p09 saves,
p10 conversion). Remaining structural opens: h02/h04/m06 (dev),
rmo_2001_2 (kit) — all fills-need-real-proofs cases.

Noise calibration (iters 0–2): per-problem flippers at 20-min caps are
c03, h05, m01 (S1 sampling luck); structural never-solved at short caps:
h01, h02, h04, m06. Single-run totals carry ±2 noise — promotions need a
composition argument or repeat runs, not just a total.

Iter-0 failure analysis (drove iter-1): all five misses (h01, h02, h04,
m04, m06) ended as S1+S2 cycles with a useless `sweep:rfl` checkpoint —
**S4 never ran** (its 900 s entry gate cannot open inside a 1080 s agent
window after S0+S1) and **gpt-oss issued zero calls** (`planned: 2,
usable: 0` every wave: the per-call guard needs `allows(timeout+60)` and
the 960 s gpt-oss timeout never fits). The loop also exits at the 600 s
tail gate stranding ~8 of 20 minutes. One coherent defect: fixed time
constants assume long windows. Fix: `Config.scaled()` multiplies the
constants by `min(1, agent_time/2400)` under the flag — identity at 40+
minute windows, so judge-cap behavior is untouched.
