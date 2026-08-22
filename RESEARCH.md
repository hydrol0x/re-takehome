# Coordination Layer — Research Notes & Design Brainstorm

*Working document for Part One (build the coordination layer) and Part Two (does
collaboration beat either model alone?). Compiled 2026-08-22 from: (a) a close
read of the kit's harness code and committed baseline runs, (b) a literature
sweep on LLM theorem proving and multi-agent coordination, (c) model research on
the two pinned models. Sources cited inline; repo evidence cited by path.*

---

## 0. TL;DR — recommended direction

**The task is a coverage problem with a perfect verifier.** Scoring is binary
and machine-checked (Comparator), and we have a cheap trusted-ish inner check
(REPL). Under a verifier, essentially all published "collaboration" gains reduce
to three things that survive evidence review:

1. **Union coverage across different model families.** Different models solve
   different problems. Already visible in the kit's own baseline runs: qwen
   7/16, gpt-oss 8/16, union **10/16**. Pooling candidates from both models is
   the single cheapest, best-evidenced coordination win.
2. **Compiler-feedback repair, capped at a few rounds, then fresh
   diversity.** One or two error-informed repair rounds are worth ~an order of
   magnitude of extra samples (Kimina, Goedel-V2, APOLLO), but repair loops
   plateau — the baselines demonstrate both failure modes (gpt-oss: 25 identical
   errors in a row; qwen: thrashing). On plateau, **hand the candidate + error
   history to the other model** — the one intervention two-model setups get
   nearly for free.
3. **Decomposition for the hard tail.** Sketch → sorry-scaffold → fill lemmas
   (Draft-Sketch-Prove / DeepSeek-Prover-V2 / Hilbert pattern) is the dominant
   architecture of every 2025-26 SOTA prover, and it's what the six
   baseline-unsolved sample problems need (they all require multi-step lemma
   structure, not a lucky tactic).

Plus one place where consensus genuinely pays because the verifier *can't* help:
**committing to an answer** for answer-type problems (a wrong answer can burn
the whole 8 h). Both models answer independently; agree → proceed, disagree →
cheap adjudication before any proof spend.

The recommended shape is a **staged escalation ladder** (cheap → expensive),
anytime, with strict safety rails imposed by harness mechanics (one transport
error permanently closes the budget ledger; a deadline kill mid-call zeroes the
problem). Explicitly rejected, with citations: multi-agent debate, MoA-style
synthesis, free-form critic agents, learned routers — all fail compute-matched
replication or are redundant given a compiler.

This design is simple to describe (one loop, three cross-model interfaces),
maps 1:1 onto ablations for Part Two, and every mechanism is motivated by a
failure already visible in the committed baseline data.

---

## 1. Ground truth from the kit

Constraints extracted from `src/re_harness/` — these shape the design more than
any paper.

### 1.1 Scoring contract

- One point iff: Comparator accepts every required declaration **and** numeric
  answers are decimal literals **and** spend ≤ $1.00 **and** finished within
  deadline (`worker.py:175`, `README.md`).
- Comparator = official `leanprover/comparator` in a fresh container: builds
  `Challenge.lean` and `Solution.lean` with lake, `lean4export`s both, requires
  kernel-level statement equality for all `theorem_names` + `definition_names`,
  and **permitted axioms only `propext`, `Classical.choice`, `Quot.sound`**
  (`lean.py:316`).
  - ⇒ `sorry` (sorryAx), `native_decide` (`Lean.ofReduceBool`), and any
    `axiom` declaration **fail final scoring**. Plain `decide` is fine (kernel
    reduction).
- `models_used` / `both_required_models_used` are recorded and *reviewed* but
  not mechanically scored (`worker.py:198`). Both models should genuinely
  participate on every problem.

### 1.2 REPL vs Comparator gap (silent-failure surface)

The inner REPL check (`services.lean.check_file`) is *not* what grades us:

| | REPL (iteration) | Comparator (grading) |
|---|---|---|
| Imports | **stripped**; body runs in a warm `import Mathlib` env (`lean.py:129`) | real file built by lake — imports matter |
| Statements | not compared to challenge | kernel-level equality required |
| Axioms | not checked | whitelist enforced |
| sorry | detected via messages | fails build/export |

⇒ The agent needs its own guards: (a) **statement splicing** — never let a
model touch the theorem statements; keep the pristine challenge declarations and
splice in only proof bodies + helper lemmas above them, so statement equality
holds *by construction*; (b) lexical ban on `sorry`/`admit`/`native_decide`/
`axiom`/`sorryAx`; (c) force the original imports in the final file.

### 1.3 Budget mechanics — and the ledger landmine

- Reservation before each call: `(request_bytes·in_price + max_tokens·out_price)·1.1`
  against ceilings A=$0.15/$0.60, B=$0.10/$0.50 per M (`models.py`, `llm.py:134`).
  `BudgetExceeded` raises **before** the call and is safe to catch.
- **Landmine:** any transport failure or HTTP ≥ 400 → `budget.mark_unknown()` →
  the ledger is *permanently closed*: every later `reserve()` raises, and final
  status becomes `cost_unknown` = **0 points even if the checkpointed proof is
  correct** (`llm.py:153-186`, `budget.py:75`, `worker.py:179`).
  - Consequences: no retry-after-failure exists; keep in-flight concurrency
    modest (a single 429/502 kills the problem's LLM access); always pass an
    explicit generous `timeout_s` (observed gpt-oss calls up to **471 s**;
    the default httpx read timeout is 180 s — `llm.py:60`); after
    `LLMCallError`, fall back to LLM-free mode (the REPL still works — the
    deterministic tactic sweep can continue) and finalize the best checkpoint.
- The `provider` block is fixed by the harness (`allow_fallbacks: false`,
  `require_parameters: true`, `max_price` at the ceilings) — we cannot pin
  providers. For gpt-oss this excludes the fast expensive hosts (Cerebras
  ~$0.69/M out, Groq $0.60/M): expect the **cheap, slow tier** (~25–40 tok/s
  observed).

### 1.4 Time mechanics — the second landmine

- Judge runs `VM_TIME_LIMIT_S=28800 VM_BUDGET_USD=1.00` (`RULES.md`). The
  worker gives the agent `time_limit − verify_reserve` (default 120 s) then
  **cancels** `solve()` (`worker.py:92-98`).
- A cancel mid-LLM-call raises through the client → `mark_unknown` → ledger
  closed → `cost_unknown` → 0 points. This is exactly how every baseline
  timeout row died (all `cost_unknown` rows in the committed summaries).
- ⇒ The agent must run its own clock: read `VM_TIME_LIMIT_S` /
  `VM_VERIFY_RESERVE_S` from the environment, never start a call that could
  outlive `deadline − margin` (margin ≥ 10 min), checkpoint on every
  improvement, and return the best candidate on its own schedule.

### 1.5 Problem formats (sample manifest)

1. **Plain theorems** (12/16): prove, statement fixed.
2. **Numeric answers** (3/16: p06, p07, p10): `abbrev pXX_answer : ℕ := sorry`
   — final body must be a *decimal literal* (regex-enforced, `lean.py:343`);
   `2^11 - 1` won't do, compute the decimal.
3. **PutnamBench-style solution abbrevs** (2/16: `Set (ℤ × ℤ)`, `ℕ → ℕ`): body
   unconstrained. **Loophole (already in the committed baselines):** gpt-oss
   passed both Putnams by defining the abbrev as the theorem's own LHS and
   proving `rfl`. Mechanically scores; see §6.6 for the policy call.
- `problem.metadata.source` names the source benchmark (miniF2F, etc.) and the
  description header leaks a tier tag — holdout likely draws from the same
  public distributions (miniF2F / PutnamBench / olympiad formalizations).

### 1.6 Rules constraints on design

- Only the two model IDs, only openrouter.ai; any sampling/reasoning params.
- No per-problem special-casing; *generic* tactic libraries and few-shot
  examples explicitly allowed (`RULES.md` Conduct) — a deterministic tactic
  sweep is legal and free.
- Python deps must be declared in `pyproject.toml` (installed before network
  lock) — e.g. `sympy` for evaluating model-proposed closed forms to decimal
  literals.
- Simplicity preference is explicit: "rather run a simple design we can fully
  understand than a complicated one that scores marginally better."

---

## 2. Empirics from the committed baseline runs

The kit ships two full baseline runs (`outputs/baseline/…`, 20-min cap era,
single-model repair loop, temp 0.2, 12 k max_tokens, ≤ 25 turns). This is the
best data we have and it's already decisive about several design questions.

### 2.1 Scores and the union effect

| | qwen3.5-flash | gpt-oss-120b | union |
|---|---|---|---|
| Solved | **7/16** | **8/16** | **10/16** |

- qwen-only solves: p06 (`set_option exponentiation.threshold` trick), p08.
- gpt-oss-only solves: p05 (knew the exact Mathlib gcd-of-Mersenne lemma),
  putnam_2018_a1 + putnam_2020_a2 (via the tautology loophole).
- **Unsolved by both (the battleground): p09, p10, rmo_2000_2, rmo_2000_3,
  rmo_2000_6, rmo_2001_2** — all need multi-step lemma structure (mod-cycle
  induction, `IsGreatest` with an induction bound, cube-sandwich case split,
  series regrouping, valuation arguments, prime case analysis).
- Caveat: gpt-oss ran under a 18-min effective cap and made only 2–7 calls on
  hard problems before being killed; its true ceiling at 8 h is higher.

### 2.2 Failure pathologies are complementary

- **gpt-oss = stable-but-stuck.** p06: 25 consecutive turns with the *identical*
  error (`unsolved goals ⊢ 7^2026 % 100 = 49` — answer right on turn 1, never
  found the kernel-options trick qwen knew). Low diversity at temp 0.2; the
  loop added no information after round ~3.
- **qwen = thrashing.** p09: 25 turns, error signature different nearly every
  turn (syntax errors, hallucinated constants like `Nat.pos_pow_of_pos`,
  `Missing cases` loops), error count oscillating 1→17. High diversity, no
  convergence, no structure.
- These are the two textbook repair-loop failure modes, and each model's
  weakness is the other's strength → concrete case for plateau-triggered
  cross-model handoff and for structure (sketematics) from the deep reasoner.

### 2.3 Error taxonomy (all baseline REPL checks, pooled)

| count | category | design response |
|---|---|---|
| 2530 | "no goals" (proof-script misalignment) | structured proof format; include goal state in repair prompts; prefer `have`-chains over long tactic scripts |
| 622 | unknown constant/identifier (hallucinated lemmas) | curated lemma cheat-sheet in prompt; `exact?` mining; "did you mean" substitution rule; cross-model handoff (recency gap, §3) |
| 294 | unsolved goals | escalate tactic strength / decompose |
| 215 | type mismatch (ℕ subtraction, coercions) | few-shot idiom examples; `omega`/`push_cast` guidance |
| 118/83 | omega / nlinarith misapplication | tactic cookbook w/ applicability notes |
| 103 | syntax errors (mostly qwen) | low-temp format pass, or qwen thinking-on |
| 29/10 | heartbeats / maxRecDepth / exponent threshold | **deterministic error→fix rules** (add `set_option` preamble) — pure harness code, zero LLM cost |

### 2.4 Cost & latency profiles (observed through this harness)

| | qwen3.5-flash | gpt-oss-120b |
|---|---|---|
| median call latency | 4–60 s (~200 tok/s) | **100–470 s** (~25–40 tok/s, cheap tier) |
| typical cost/call | $0.0002–0.002 | $0.0005–0.0017 |
| worst per-problem spend (25-turn loop) | $0.05 | $0.007 |
| reasoning tokens in baseline | **0 (thinking off!)** | ~5 k median (default effort) |
| quirks | `finish_reason: length` truncations at 12 k; occasional Alibaba content-filter 502s inside HTTP-200 responses (wasted call, ledger survives) | none observed beyond slowness |

**Budget reality: $1 ≈ 20–150× the worst observed per-problem spend.** Money is
not the binding constraint; *wall-clock for gpt-oss serial chains* and *model
capability* are. Practical planning numbers: ~$1 buys ≈ 3.8 M qwen output
tokens or ≈ 5.9 M gpt-oss output tokens (cheap route); 8 h fits ~60–200 serial
gpt-oss high-effort calls or ~500–1500 qwen calls, times 2–4× with modest
concurrency. REPL checks (serial, warm Mathlib env) ran 0–10 s on baseline
candidates, 120 s cap per check.

### 2.5 Two untapped capability levers found in the baseline config

1. **qwen ran with thinking off** (0 reasoning tokens everywhere). Qwen3.5-Flash
   is a hybrid thinking model; `reasoning: {enabled: true}` (or effort mapping)
   is available through the harness and was never used.
2. **gpt-oss ran at default (medium) effort.** Model card: AIME 2025 = 80.0
   medium → **92.5 high**. `reasoning: {effort: "high"}` is a large math upgrade
   we get for tokens, not architecture.

---

## 3. The two models

From web research (OpenRouter pages, model card, MathArena, Artificial
Analysis, community evals) + kit observations. Numbers marked (r) are reported
by aggregators and worth a cheap sanity check during calibration.

### 3.1 `qwen/qwen3.5-flash-02-23` (Model A)

- Hosted flavor of Qwen3.5-35B-A3B (~35B total / ~3B active, MoE +
  linear-attention hybrid), released 2026-02; 1 M context, ~65 k max completion
  (harness caps `max_tokens` at 32 k anyway). Single provider (Alibaba Intl).
- ~$0.065/M in, $0.26/M out via OpenRouter (r).
- **Hybrid thinking**: `reasoning.enabled`/`max_tokens` map to Alibaba's
  `enable_thinking`/`thinking_budget`; effort maps to budget ratios (r).
  Thinking tokens bill as output.
- Math: no official Flash benchmarks; family band ≈ high-80s/low-90s AIME with
  thinking (r); Artificial Analysis Intelligence Index ~30 for 35B-A3B
  (reasoning) vs 24 for gpt-oss-high (r); family notably robust on harder
  comps (HMMT) relative to gpt-oss.
- **Lean: no direct published results, but a 2026 training cutoff** — it knows
  current Lean 4 / Mathlib idioms. Observed concretely: it found
  `set_option exponentiation.threshold` (a modern option) that gpt-oss (June
  2024 cutoff) never produced in 25 tries.
- Weaknesses: thrashy repair behavior, syntax slips, hallucinated lemma names,
  truncation if `max_tokens` set low, occasional content-filter false
  positives, single-provider dependency.

### 3.2 `openai/gpt-oss-120b` (Model B)

- Open-weight MoE, 116.8 B total / 5.1 B active, Aug 2025, text-only, 131 k
  context, harmony format (OpenRouter splits `reasoning`/`content`).
- Effort low/medium/high; **AIME 2025 no-tools: 50.4 / 80.0 / 92.5** (model
  card); GPQA-D 80.1 high; HMMT ≈ 76.7 (r) — drops on harder tiers.
- **Direct Lean 4 evidence**: a June-2026 UW eval (arXiv 2606.05632) found it
  among the most cost-efficient models tested for Lean formalization
  (< $0.01 per correct proof; their config: **temp 1.0, up to 30
  compiler-feedback repair iterations**) (r); used as the informal reasoner in
  the Discover-and-Prove PutnamBench pipeline (arXiv 2604.15839) (r).
- Through this harness's price ceiling we get the cheap/slow provider tier:
  ~$0.17/M out effective, 2–8 min per high-effort call.
- Weaknesses: stale Mathlib knowledge (June-2024 cutoff → deprecated lemma
  names), stuck-loop repair behavior at low temp, occasional repetition in long
  traces, knowledge-hallucination tendency, harmony-format leakage quirks
  (mitigate: parse `content`, extract last ```lean block).

### 3.3 Complementarity (the actual case for two models)

| axis | qwen3.5-flash | gpt-oss-120b |
|---|---|---|
| wall-clock per call | **~10× faster** (our tier) | slow |
| $ per attempt | cheap | **cheapest** |
| math depth (with reasoning on) | strong, family-best on hard comps | strong at high effort, elite AIME band |
| Lean/Mathlib recency | **2026 cutoff — current idioms, set_options** | 2024 cutoff — deprecated names |
| Lean evidence | indirect | **direct (cost-efficient prover)** |
| repair behavior | diverse/thrashy (explorer) | focused/stuck (exploiter) |
| failure independence | different family, different training | different family, different training |

This is a *portfolio* argument, not a fixed role split: both models do both
jobs, with emphasis — gpt-oss-high for deep solving and first-shot proofs
(sample-efficient, dirt cheap, slow), qwen-thinking for hard-math second
opinions and as the fast repair/iteration workhorse, qwen-fast (thinking off)
for cheap sweeps and formatting. Cross-model handoff exploits the recency gap
and the explorer/exploiter contrast.

### 3.4 Recommended starting settings (to calibrate in week 1)

- qwen: solving `reasoning:{enabled:true, max_tokens:16-24k}`, `max_tokens`
  24–32 k, temp ~0.7–1.0 for sampling diversity; sweeps/format passes
  thinking-off, temp 0.7, `max_tokens` ≥ 16 k (avoid the observed 12 k
  truncations); explicit `timeout_s ≥ 300`.
- gpt-oss: `reasoning:{effort:"high"}` for solve/sketch, `"medium"` for repair
  iterations; temp ~1.0 for proof search (per UW config); `max_tokens` 24–32 k;
  explicit `timeout_s ≥ 900` (observed 471 s calls; default 180 s read timeout
  would close the ledger).
- Never send a request whose reservation could trip `BudgetExceeded` near the
  cap — check remaining budget first and shrink `max_tokens` for final calls.

---

## 4. Literature: what the evidence supports (and what it rejects)

Full agent reports with URLs are summarized here; the key filter is:
**our verifier converts "collaboration" into a coverage-per-dollar question.**
Most published multi-agent gains were measured where the hard part is *judging
answers* — a problem we don't have.

### 4.1 Components with replicated positive evidence (adopt)

1. **Repeated sampling vs a verifier ("Large Language Monkeys",
   arXiv 2407.21787):** coverage scales log-linearly over orders of magnitude;
   with an exact verifier it converts directly to accuracy. This is the
   backbone of every SOTA prover (DeepSeek-Prover-V2, Kimina, Goedel-V2) and
   the null hypothesis every fancier mechanism must beat at equal cost.
2. **Cross-family union coverage (arXiv 2510.21513, code gen/repair, 10
   models):** union-of-candidates up to +83 % over best single model; two-model
   ensembles realize ~95 % of the diversity benefit; cross-*family* pairs are
   the most disjoint. The "selection bottleneck" result (arXiv 2603.20324):
   diversity pays exactly when the selector is good — ours is perfect.
   Matches our observed 7/8/10 union.
3. **Compiler-feedback repair, few rounds (in-domain):** Kimina-72B pass@32
   84.0 → 86.4 with *one* error-fix round ≈ pass@1024 (~16× sample
   efficiency); Goedel-Prover-V2 +2.4pp from 2 rounds at ~25 % extra tokens;
   APOLLO (arXiv 2505.05758): general models jump 3–7 % → 40 %+ on miniF2F
   when the compiler localizes errors and sub-lemmas are isolated (~100×
   sample efficiency); Delta Prover's ablation (arXiv 2507.15225): at a fixed
   1024-sample budget, iterative repair consistently beats best-of-N.
   **Counterweight (Olausson, arXiv 2306.09896): at equal token budget
   self-repair can lose to fresh resampling** — the generic-code result;
   in Lean the compiler supplies the expert feedback that made repair win in
   Olausson's own ablation. Consensus depth is shallow: 2–3 rounds per
   candidate, then sorrify-and-recurse or re-diversify (§4.4 Mechanic).
4. **Cross-model handoff of a stuck problem *with* accumulated error history:**
   the closest measurement (Olausson feedback ablation: stronger-model feedback
   on weaker model's code, 50 % → 54 % at fixed budget) plus Tyen et al.
   (arXiv 2311.08516): LLMs are bad at *locating* errors but good at *fixing
   located* errors — the compiler locates for free, and model B's value is
   different priors, not critique. Keep it one-directional and event-triggered
   (plateau), not a standing dialogue.
5. **Decomposition on failure (informal solve → formal sketch with `sorry`
   holes → fill):** Draft-Sketch-Prove (arXiv 2210.12283); DeepSeek-Prover-V2
   (arXiv 2504.21801) — V3 sketches subgoals, small prover fills; Prover Agent
   (arXiv 2506.19923) — informal reasoner + prover + auxiliary lemmas, 88.1 %
   miniF2F at small sample budgets; Hilbert (arXiv 2509.22819) — **two
   different provers** + recursive decomposition, 99.2 % miniF2F / 70 %
   PutnamBench; Seed-Prover's light/medium/heavy escalation ladder
   (arXiv 2507.23726). The 2026 trend is *simpler* scaffolds (Leanstral 1.5:
   plain agent loop + compiler → 100 % miniF2F) — evidence for the graders'
   simplicity preference, and for ours.
6. **Verifier-gated cascade (FrugalGPT, arXiv 2305.05176; agreement-based
   cascading, arXiv 2407.02348):** cheap model first, escalate on failure. The
   hard part of cascades — the deferral scorer — is solved by the compiler.
7. **Self-consistency for the one unverifiable decision** (Wang,
   arXiv 2203.11171): majority/agreement across models for *answer
   commitment* only. Caveat (arXiv 2403.02419): voting is non-monotonic on
   hard queries — so treat disagreement as "escalate", not "outvote".

### 4.2 Considered and rejected, with reasons (cite in the report)

- **Multi-agent debate:** fails compute-matched replication repeatedly (Huang
  arXiv 2310.01798; Smit arXiv 2311.17371; "Stop Overvaluing MAD"
  arXiv 2502.08788; more rounds *hurt*: arXiv 2502.19130). The compiler is our
  judge; debate buys agreement dynamics we don't need.
- **MoA-style synthesis/aggregation:** Self-MoA (arXiv 2502.00674) beats mixed
  MoA; synthesis won 0/42 tasks in arXiv 2603.20324. Union + exact selection
  captures the diversity value without an aggregator.
- **Free-form critic agents / round-robin refinement:** redundant next to a
  compiler (Tyen); refinement without external signal degrades (Huang). The
  one legit critique role in the literature — statement-faithfulness
  (CriticLean, arXiv 2507.06181) — is mostly moot here because *statements are
  fixed by the challenge file*; it survives only as the answer-commitment gate.
- **Learned routers / bandit compute allocation / optimal stopping:** training
  we can't do; marginal vs stop-on-success + a fixed ladder (arXiv 2510.01394,
  2506.12721).

### 4.3 Cost-allocation evidence

- Small-model-many-samples is compute-Pareto-optimal at low budgets (Wu,
  arXiv 2408.00724; Snell, arXiv 2408.03314) — but flips on very hard problems
  where the weak model's coverage curve plateaus below threshold. Maps cleanly
  to: qwen volume early, gpt-oss-high depth later, decomposition for the tail.
- With a slow verifier, candidate *deduplication* and cheap pre-filters
  (syntax/lexical guards before REPL) matter; REPL throughput (~120 s cap,
  serial) is a first-class resource over 8 h.
- Sample-count guidance from prover curves: most of pass@k's value arrives in
  the first dozens of samples per (sub)goal (DeepSeek/Goedel curves); beyond
  ~32–64 whole-proof samples per goal is wasted at our budget — spend on
  repair/decomposition instead.

### 4.4 Agentic Lean loops with general models — the 2025-26 evidence base

The field converged on exactly our setup (general chat model + REPL loop), and
the wrapper, not the weights, is what unlocks it:

| system | backbone (no fine-tune) | result | transferable idea |
|---|---|---|---|
| Delta Prover (2507.15225) | stock Gemini 2.5 Pro | **95.9 % miniF2F**, SOTA over fine-tuned provers | at fixed 1024-sample budget, **repair beats best-of-N** (their ablation) |
| LEAP (2606.03303) | Gemini 3.1 Pro | Putnam 2025 **0/12 → 12/12** | NL blueprint as a lemma **DAG**, formalize node-by-node |
| Minimal Agent / AxProverBase (2602.24273) | Claude Opus 4.5 | **54.7 % PutnamBench pass@1** cheaply | one *stateful evolving attempt* (≈50 iterations) with failure-memory + a Reviewer that checks the statement wasn't mutated |
| APOLLO (2505.05758) | o3/o4-mini | 3–7 % → **40 %+** miniF2F | rule-based syntax fixes → **sorry-isolation of broken sub-lemmas** → tactic cascade per hole → LLM only on survivors; depth ≈ 2 |
| Mechanic (2603.24465) | — | efficiency on IMO/Putnam-class | the **"sorrifier"**: never regenerate a partly-good proof and never grow endless repair context — surgically replace broken regions with `sorry`, recurse on holes |
| DSP+ (2506.11487) | R1/QwQ + BFS-prover | 80.7 % miniF2F training-free | **mask broken sketch lines, keep the rest** |
| HILBERT (2509.22819) | Gemini 2.5 Pro + Goedel-32B | 99.2 % / 70 % Putnam | ablation: **informal-reasoner quality binds, not prover strength**; retrieval *reduces* cost |
| DAP "Discover & Prove" (2604.15839) | **gpt-oss-120b** as discoverer | first 36 hard-mode PutnamBench | answer discovery as its own stage (temp 1.0, ~30 cheap NL self-checks), then rewrite to easy-mode |
| ECP (2505.18492) | GPT-4.1-mini | answer accuracy 14.5 → 45.1 % | LLM writes an **enumeration program** for small cases → conjecture closed form → admissibility-check in Lean before proving |
| ETH-SRI cost-router (2606.04883) | — | **−28.9 % cost** at equal PutnamBench | restart-vs-continue policy; heuristic version: *same error class twice → re-decompose* |
| LeanSearch-v2 downstream ablation (2605.13137) | same loop ± retrieval | **4 % → 20 %** proof success | lemma-name retrieval is the single biggest fix for hallucinated names (offline substitute for us: static Mathlib name index + in-REPL `exact?`) |

Additional practical consensus (leanprover/skills, kimina-lean-server, Goedel
eval configs): force the header/statement yourself and let the model write only
proof bodies; shallow repair (2–3) then re-diversify; warm-REPL reuse is the
biggest wall-clock lever (our harness already provides it); check acceptance
with `#print axioms` (catches `native_decide`); Seed-Prover 1.5 persists a
per-problem pool of *proven lemmas* across attempts — very valuable over 8 h.

**Calibrated expectation for our backbones:** the strong table rows use
frontier reasoners. With qwen3.5-flash + gpt-oss-120b, published analogues
(APOLLO on o4-mini, Prover Agent with small models, DAP with gpt-oss-120b)
put us in the "most easy/AMC tier + some RMO/Putnam-A1 tier, little IMO tier"
band — consistent with the sample-set spread and worth saying plainly in the
report.

---

## 5. Design space considered

| option | sketch | verdict |
|---|---|---|
| **A. Union of solo baselines** | run each model's repair loop, submit first acceptance | floor (~10/16-equiv); keep as ablation control, not the design |
| **B. Escalating portfolio + handoff + decomposition** | staged ladder below | **recommended** — every stage evidence-backed & individually ablatable |
| C. Fixed role split (solver=gpt-oss, formalizer=qwen) | hard-coded pipeline roles | rejected as *fixed* structure: evidence says both models are credible at both jobs (qwen knows modern Mathlib; gpt-oss has direct Lean cost-efficiency evidence); keep roles as *emphases* inside B |
| D. Debate / critique layers | models review each other's proofs | rejected on evidence (§4.2); compiler judges |
| E. Heavy search (tree/MCTS over tactics) | per-tactic search via REPL | rejected: REPL is file-level (no goal-state stepping API in this kit), serial, 120 s/check; wrong tool for the harness; whole-file + decomposition fits the interface |

*Design principle carried through:* the coordination layer is **one loop and
three narrow cross-model interfaces** — (i) pooled diverse sampling, (ii)
answer consensus gate, (iii) plateau handoff — plus decomposition as the
expensive tail stage. No free-form inter-model dialogue.

---

## 6. Recommended architecture (v1)

### 6.0 Shape

```
solve(problem):
  guardrails: soft_deadline = start + (VM_TIME_LIMIT_S − VM_VERIFY_RESERVE_S) − 600 s
              stop-LLM margin; checkpoint every improvement; finalize best.

  S0  Deterministic sweep ($0):      statement-spliced tactic cocktail
      (norm_num / simp / omega / decide+set_options / nlinarith+hints /
       positivity / field_simp;ring / aesop / interval-style combos)
      → REPL-check ~15 templates. Solves the trivial tier free.

  S0.5 (answer problems only) Answer protocol (ECP/DAP pattern — DAP literally
      uses gpt-oss-120b for this stage):
      qwen-think and gpt-oss-high independently produce answer as closed form
      + reasoning; harness evaluates closed forms to decimals (sympy);
      agree → commit; disagree → one adjudication round (each sees both
      derivations), still split → cheap arbitration: REPL falsification
      probes (decide/plausible on small instances) and/or sandboxed
      enumeration of small cases (model-written, restricted exec, no
      network — network is locked anyway).
      Candidate answers can also be screened by answer-swap: fix the file,
      swap only the abbrev body, recheck (BASE, arXiv 2606.15972).

  S1  Cheap diverse sampling: qwen (thinking-off, temp ~0.8) k≈8 whole-file
      candidates + qwen-think k≈2 + gpt-oss-medium k≈2 in parallel;
      dedupe; lexical guards; REPL-check in "closeness" order.

  S2  Targeted repair: for the few nearest-miss candidates (fewest errors,
      errors latest in file): ≤2–3 error-informed rounds with the model that
      wrote them, deterministic error→fix rules applied first (set_option
      insertions, "did you mean" substitutions) — those are free.

  S3  Plateau handoff: if error signature repeats or a model's rounds stop
      progressing → other model gets the candidate + distilled error history
      (not a critique dialogue; a fresh attempt with more information).
      Also: fresh re-sampling beats endless repair (Olausson) — alternate.

  S4  Decompose (hard tail, the 8 h weapon):
      gpt-oss-high (and qwen-think as second sketcher) writes NL solution +
      Lean skeleton: *standalone, explicitly-typed helper lemmas* + main
      proof using them, all bodies `sorry`.
      (Explicit lemma statements, because the harness REPL wrapper surfaces
       only messages — not goal states at sorries — so the skeleton itself
       must carry each hole's exact goal.)
      REPL validates the skeleton (sorry-warnings OK, errors not); broken
      skeleton lines are masked/re-fixed (DSP+), not discarded.
      Fill holes independently: tactic cascade first (free), then qwen
      sweeps each hole cheaply, stuck holes escalate to gpt-oss-high;
      ≤2 repairs per candidate, then Mechanic-style sorrify deeper or
      re-decompose that lemma.
      Proven lemmas are cached in a per-problem pool and reused across
      skeletons (Seed-Prover pattern); restart heuristic: same error class
      twice → new decomposition (ETH-SRI cost-router, heuristic form).
      Assemble, final repair rounds, iterate with new sketches while
      time remains.

  S5  Endgame: at soft deadline − headroom: stop new LLM calls, re-verify the
      best candidate via REPL, restore statements/imports, enforce literal
      answers, checkpoint, return.
```

Per-problem budget envelope (generous): S0 $0 · S1 ≈ $0.02 · S2–S3 ≈ $0.10 ·
S4 ≈ $0.4–0.7 across many sketch/fill cycles · reserve ≈ $0.1. Wall-clock
dominated by gpt-oss latency and serial REPL checks; qwen work overlaps
gpt-oss waits (concurrency ≤ 3–4 for ledger safety).

### 6.1 Why each cross-model interface exists (evidence + observed)

1. **Pooled sampling (S1):** union coverage, cross-family diversity
   (arXiv 2510.21513; observed 7/8→10 union).
2. **Answer gate (S0.5):** the only decision the verifier can't check cheaply;
   wrong answer = unbounded wasted proof search (observed: gpt-oss had the
   *right* answer in 1 turn on p06 and still burned 24 turns on the proof —
   imagine the converse with a wrong answer).
3. **Plateau handoff (S3):** stuck-vs-thrash asymmetry (observed p06/p09);
   recency gap (qwen knows current Mathlib options; gpt-oss doesn't);
   error-history transfer (Olausson/Tyen).
4. **Sketch/fill (S4):** the SOTA pattern (DSP→DeepSeek-V2→Hilbert), matched
   to the six unsolved sample problems, all of which need lemma structure.
   Concrete fits: p10 = two lemmas (membership by `norm_num`; `∀ n ≥ 7,
   3^n ≤ n!` by induction); p09 = mod-cycle lemma (`2^n % 7 = 2^(n%3) % 7`)
   + 3-case finish; rmo_2000_2 = cube-sandwich (`(x+2)³ ≤ RHS < (x+3)³` for
   x ≥ 9-ish) → `y = x+2` → quadratic, each step nlinarith/omega-sized.

### 6.2 Deterministic force multipliers (zero LLM cost, all rules-legal)

- **Statement splicing** (§1.2) — kills silent statement drift.
- **Tactic cocktail sweep** (S0) — generic tactic library, explicitly allowed.
- **Error→fix rewrite rules**: `exponent … exceeds the threshold` → insert
  `set_option exponentiation.threshold`; `maximum recursion depth` →
  `set_option maxRecDepth`; heartbeats → `set_option maxHeartbeats`;
  `unknown constant X — did you mean Y` → substitute; strip trailing tactics
  after "no goals" errors where recoverable.
- **Lexical guards**: ban `sorry|admit|native_decide|axiom`; force original
  imports; enforce decimal-literal answers by splicing the computed literal.
- **REPL as a tool**: `exact?`/`hint` suggestion mining for a stuck hole;
  `plausible`/`decide` falsification probes for candidate lemmas/answers
  before spending proof effort (the image ships plausible; LeanSearchClient
  and polyrith need network → unusable; `exact?` is offline and fine).
- **`#print axioms <thm>` acceptance gate** appended to the final REPL check —
  deterministically catches `native_decide`/stray axioms before submission.
- **Static Mathlib name index** shipped in the repo (built offline from the
  pinned Mathlib version): fuzzy-match hallucinated names → real ones before
  burning a repair round. Retrieval is the best-evidenced fix for the #1
  semantic error class (4 %→20 % in the LeanSearch-v2 ablation); a static
  index + `exact?` is the offline approximation. Generic data — rules-legal.
- **sympy evaluation** of model-proposed closed forms → decimal literals.
- **Candidate dedup + syntax pre-filter** before REPL (REPL time is scarce).
- **Per-problem "lab notebook"** (Minimal Agent pattern): a compact running
  digest of tried strategies + failure lessons, included in later prompts —
  state, not dialogue.

### 6.3 Safety rails (from §1.3–1.4)

- Self-deadline with ≥ 10 min margin; no call started that can't finish.
- Explicit `timeout_s` on every call (qwen ≥ 300 s, gpt-oss ≥ 900 s).
- Concurrency cap 3–4; catch `BudgetExceeded` → finalize; catch `LLMCallError`
  → LLM-free mode (deterministic stages still run) → finalize.
- Checkpoint policy: best = accepted > fewest-errors > syntactically-valid;
  checkpoint on every improvement; final answer always re-verified in REPL
  before return.
- Detect qwen content-filter pseudo-failures (finish_reason=error inside 200)
  and treat as a wasted sample, not a crash.

### 6.4 What "both models genuinely used" means here

Every problem: both models appear in S1 by construction; answer problems use
both in S0.5; S3/S4 route by state. `result.json.models_used` will show both;
metadata records which stage/model produced the accepted proof (feeds Part 2).

### 6.5 Simplicity story (for the report)

One loop; stages are pure functions candidate→candidate; three narrow
interfaces; no dialogue protocols; every stage has an on/off switch (ablation);
~500–800 lines of agent code on top of the kit.

### 6.6 The tautology loophole (policy decision to make explicitly)

For non-numeric solution abbrevs, defining the abbrev as the theorem's LHS and
proving `rfl` passes the Comparator (the committed gpt-oss baseline already
does this on both Putnams). Options: (a) never use it; (b) honest-first,
tautology as last-resort fallback with transparent metadata; (c) always.
Recommendation: **(b)** — attempt real closed forms (both models propose;
falsification probes filter), fall back only if the honest route fails by
T−90 min, and disclose in the report. It's within the mechanical rules and
already present in the kit's own baselines, but graders read transcripts —
transparency is the right posture for a research-engineer take-home. (The
grading-gap genre is documented: "Faults in Our Formal Benchmarking",
arXiv 2606.29493, catalogs exactly this class of trivial/adversarial
solutions that harnesses must decide to reject or accept.)
*(Also: don't over-invest — holdout may contain zero such problems.)*

---

## 7. Part Two: experiment plan (does collaboration beat solo?)

Methodology per "AI Agents That Matter" (arXiv 2407.01502): compare at
**matched dollar/time budget**, same scaffold everywhere, report curves not
points.

### 7.1 Arms (all on the 16 sample problems, same ladder code)

1. `solo-qwen`: the *same* ladder with only qwen working (S1 all-qwen, S3
   handoff → self with fresh context, S4 sketch+fill both qwen). One model
   type at a time, budget/time matched — this isolates coordination from
   scaffolding.
2. `solo-gptoss`: same with only gpt-oss.
3. `duo`: full system.
4. Ablations of duo (only if budget allows, in order of interest):
   `duo − handoff`, `duo − answer-gate`, `duo − decompose`,
   `duo − deterministic-sweep`.

### 7.1b Frontier reference baseline (Claude / Fable 5)

Separately from the scored arms, have a frontier model (Claude Fable 5) write
Lean proofs for all 16 sample problems, verified through the same REPL +
`rescore.sh`. Purpose:

- **Solvability calibration**: separates "our small models are too weak" from
  "this formalization is inherently nasty at any capability level" — i.e., an
  approximate ceiling for the sample set, and a sanity check that the six
  unsolved problems are provable with reasonable Mathlib machinery at all.
- **Scaffold debugging**: exercises guards/REPL/rescore paths independent of
  small-model noise.
- **Report context**: a "frontier reference" row in Part 2's table frames what
  the two-small-model system does and doesn't recover.

Rules posture: this is development/analysis tooling, not part of the submitted
runtime system (which may only call the two pinned models via OpenRouter).
Claude-assisted development is explicitly permitted with disclosure
(`RULES.md` Conduct). Guardrail: keep Claude-written *sample-problem proofs*
out of the runtime prompts — few-shot exemplars in the agent must stay generic
(idiom patterns like "induction bound", "mod-cycle", "IsLeast via
interval_cases"), never keyed to specific problems.

### 7.2 Metrics

- Solves (Comparator-verified via `rescore.sh`), with per-problem attribution:
  which stage + which model produced the accepted proof.
- Solved-vs-spend and solved-vs-wallclock curves (anytime profile from events).
- Union/overlap analysis: `solved(duo) vs solved(A∪B solo)` — the honest test
  of *coordination* beyond *portfolio*.
- Diversity accounting: distinct error signatures explored per $ (explains
  *why* union works).
- Paired significance: McNemar on problem-level outcomes (n=16 is small — 
  report exact counts and be honest about power; consider 2 seeds on the
  cheap stages).

### 7.3 Expected honest findings (pre-registered guesses)

- Scaffold + compiler + more budget does most of the lifting over the naive
  baselines (literature predicts this; say it plainly).
- Union/portfolio effect: real but modest (+2–3 problems on this sample).
- Handoff + decomposition: the marginal contributors on the unsolved-six tier;
  attribution will show whether they pay.
- Conversation-style coordination: we don't build it, citing the negative
  evidence — that *is* a finding for Part 2's "why" question.

### 7.4 Dev-budget plan ($50 key)

- ~$5 calibration (model settings, prompt formats, answer-gate reliability,
  provider latency measurement).
- ~$30 experiment arms (a full-16 duo run realistically costs $2–4; solo arms
  similar; use `VM_TIME_LIMIT_S`≈3600–7200 for iteration, full 28800 only for
  final validation on the stubborn tail).
- ~$10 final full-cap validation + holdout-sim rehearsal (fresh key
  semantics, `judge_check.sh`).
- ~$5 reserve. Track via OpenRouter ledger; the harness events give per-call
  actuals.

### 7.5 Local run mechanics

- `--n-workers 4` for sample-set runs (each worker ~5 GB RAM + a Lean
  container); rescore with `scripts/rescore.sh`; always `judge_check.sh`
  before submitting.

---

## 8. Risks & open questions

1. **gpt-oss latency tail** (2–8 min/call, no provider control): S4 must
   overlap gpt-oss sketch calls with qwen fill work; measure early. If worse
   than observed, shift sketching share to qwen-think.
2. **qwen thinking-mode via OpenRouter**: reasoning-param mapping and returned
   reasoning need a $0.10 calibration probe (agent report says enabled/budget
   map through; observed baseline never used it).
3. **Ledger fragility under concurrency**: one 429/5xx bricks a problem's LLM
   access. Calibrate concurrency on the dev key; consider serializing calls to
   each provider; keep the deterministic stages as the safety net.
4. **REPL/Comparator drift**: mitigated by statement splicing + axiom guards +
   final REPL re-verify; residual risk small (comparator builds with the same
   pinned image).
5. **Holdout difficulty mix unknown**: ladder is anytime and per-problem
   adaptive, so a harder mix costs time, not correctness; the deterministic
   sweep + S1 guarantee cheap coverage of an easier mix.
6. **Sample-size honesty in Part 2**: 16 problems → wide intervals; frame
   conclusions as effect estimates with uncertainty, backed by per-problem
   attribution stories rather than aggregate claims alone.
7. **`native_decide`/axiom leakage**: guarded lexically; also re-verify final
   candidates with `#print axioms`-style REPL probe if cheap.

---

## 9. Next steps (implementation order)

1. Skeleton agent: guards, clock, checkpointing, finalize path (no LLM) —
   plus `judge_check.sh` green.
2. S0 sweep + S1 pooled sampling + S2 repair (this alone should match/beat
   union-of-baselines on samples).
3. Calibration probes (qwen thinking, gpt-oss high, latency, answer gate).
4. Frontier reference baseline: Claude-written proofs for the 16 sample
   problems, REPL-verified (also validates the six unsolved ones are
   provable, and debugs the rescore path).
5. S0.5 answer protocol + sympy literal pipeline.
6. S3 handoff + plateau detection (error-signature hashing).
7. S4 sketch/fill with lemma cache + notebook + restart heuristic.
8. Part-2 experiment runs (solo arms first, then duo, then ablations) +
   report.

---

## 10. Experiment log

### 2026-08-22 — S0 deterministic sweep, full sample set (zero LLM cost)

`SUBMISSION_DISABLE_LLM=1`, 900 s cap, 2 workers. **6/16 passed, $0.000000,
~45 s/problem**: p01–p05, p08. Winning tactics: `linarith` (p01, p02),
`nlinarith [sq_nonneg …]` generic hints (p03, p08), plain `nlinarith` (p04),
plain `norm_num` (p05 — which the qwen baseline failed in 25 paid turns).
`judge_check.sh` passes end-to-end on the S0 path alone.
Implication: the free tier already covers the easy third of a holdout-like
mix; every LLM dollar goes to the middle and hard tiers.

### 2026-08-22 — Frontier reference proofs (Claude-written, comparator-verified)

Four of the six both-baselines-failed problems are now **proved** and pass the
Comparator on the pinned image (see `reference/`): p09 (mod-cycle lemma +
omega case bash), p10 (answer 6 + `Nat.le_induction` bound), rmo_2000_2
(cube sandwich via zify/nlinarith), rmo_2001_2 (divisor-pair analysis with a
reusable `dvd_prime_mul_prime` helper). Each took 1–3 REPL iterations —
evidence that the S4 sketch shapes are right, and a measured ceiling for
Part 2's frontier-reference row.

**rmo_2000_6 is unprovable as formalized**: part (b) asserts
`IsLeast … 20`, but `(a,b) = (5,2)` gives `5³·2⁴ = 2000`, so 10 is in the
set. A falsity certificate compiles (`reference/rmo_2000_6_falsity.lean`).
Consequences: (a) it is a guaranteed 0 for every submission — cap realistic
sample-set ceilings at 15/16; (b) cheap `decide`/`plausible` falsification
probes detect this class instantly, which the answer-gate exploits; (c) the
holdout may contain similar statement flaws (cf. "miniF2F-Lean Revisited"),
so the agent should never burn its full budget refusing to disprove.

Still open: rmo_2000_3 (heavy Finset partition work), honest Putnam closed
forms (tautology route already passes mechanically).

### Status: agent v1 (`submission/agent.py`)

Rails + S0 sweep + S1 pooled sampling + S2 repair with deterministic
error→fix rules implemented; arm switch (`SUBMISSION_MODELS=duo|qwen|gptoss`)
for Part-2 experiments; `scripts/calibrate.py` ready for the first keyed run.
S1/S2/S3/S4 live validation blocked on OpenRouter key availability in the
execution environment.

## Appendix A: source-of-truth pointers (repo)

- Landmines: `src/re_harness/llm.py:134-186` (reservation, mark_unknown),
  `budget.py:75`, `worker.py:92-98,175-185` (cancel → cost_unknown; passed
  logic), `config.py` (env knobs), `lean.py:113-155` (REPL semantics),
  `lean.py:297-341` (comparator invocation), `lean.py:343` (literal check).
- Baseline evidence: `outputs/baseline/*/summary.json` (scores),
  `outputs/baseline/openai/gpt-oss-120b/p06_pow_mod/events.jsonl` (stuck loop),
  `outputs/baseline/qwen/.../p09_imo1964/events.jsonl` (thrash loop),
  `outputs/baseline/openai/.../putnam_2018_a1/solution.lean` (tautology).

## Appendix B: key external references

Coordination: 2407.21787 (Monkeys) · 2510.21513 (ensemble union) · 2603.20324
(selection bottleneck) · 2306.09896 (self-repair limits) · 2311.08516 (error
location vs fixing) · 2305.05176 (FrugalGPT) · 2203.11171 (self-consistency) ·
negative results: 2310.01798, 2311.17371, 2502.08788, 2502.19130, 2502.00674 ·
2407.01502 (agent evaluation methodology).
Lean systems: 2210.12283 (DSP) · 2506.11487 (DSP+) · 2504.21801
(DeepSeek-Prover-V2) · 2505.05758 (APOLLO) · 2506.19923 (Prover Agent) ·
2507.23726 / 2512.17260 (Seed-Prover, 1.5) · 2509.22819 (Hilbert) ·
2507.15225 (Delta Prover) · 2606.03303 (LEAP) · 2602.24273 (Minimal
Agent/AxProverBase) · 2603.24465 (Mechanic/sorrifier) · 2606.04883 (ETH-SRI
cost-router) · 2508.03613 (Goedel-V2) · Kimina-Prover report · Leanstral 1.5 ·
2606.05632 (UW Lean eval; gpt-oss cost-efficiency) · 2604.15839
(Discover-and-Prove; uses gpt-oss-120b) · 2505.18492 (ECP) · 2606.15972
(BASE answer-swap) · 2605.13137 (LeanSearch-v2 retrieval ablation) ·
2510.11986 (conjecturing as a separate step) · 2606.29493 (Faults in Formal
Benchmarking) · github.com/leanprover/skills · kimina-lean-server.
Models: gpt-oss model card (2508.10925) · OpenRouter model/provider pages ·
MathArena · Artificial Analysis.
