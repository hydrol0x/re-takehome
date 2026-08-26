# Experiment log (live runs)

Chronological record of keyed runs. Design + offline experiment history:
`RESEARCH.md` §10. Environment specifics for the web dev container:
`RUNBOOK.md` appendix.

## 2026-08-23 · Calibration (dev container)

Probes: `scripts/calibrate.py` (+ a follow-up gpt-oss retry probe).
Spend: ≈ $0.004 total. Artifacts: `outputs/calibration-*.json`,
`outputs/gptoss-retry-probe.events.jsonl`.

Findings:

1. **qwen3.5-flash thinking control**: `reasoning: {enabled: true}` alone
   does NOT engage thinking (0 reasoning tokens), and neither does
   `reasoning: {effort: high}`. Only an explicit budget works:
   `{enabled: true, max_tokens: 4000}` → 3255 reasoning tokens. The agent's
   `qwen-think` profile already passes a budget — configuration confirmed
   correct.
2. **qwen without thinking still answered 7^2026 mod 100 = 49 correctly** in
   every probe (~15 s, ~3 k tokens, ~$0.0008/call) — the cheap tier is
   genuinely capable on computational questions.
3. **gpt-oss upstream 429s are real**: the very first gpt-oss call hit
   "temporarily rate-limited upstream" (CoreWeave shared pool,
   `allow_fallbacks: false` prevented rerouting) and — as designed by the
   harness — permanently closed that ledger. Four spaced retries then all
   succeeded (2–6 s at low effort, ~$0.00002/call, correct answers).
   Per-call spot risk during the burst ≈ 1 in 5.
4. **Agent hardening applied in response**: S1 now runs the full qwen wave
   (generate + check) before the first gpt-oss call ("value before risk");
   S0.5 asks qwen before gpt-oss; gpt-oss calls are serialized with a 5 s
   minimum gap. A ledger-closing 429 can now cost at most the not-yet-run
   gpt-oss share of a problem, never qwen's banked work.
5. The fail-closed ledger + LLM-free degradation path triggered exactly as
   designed during the first failed calibration — live validation of the
   §1.3 landmine analysis.

## 2026-08-23 · Part-2 arms at matched 30-min caps (full sample set)

Same ladder code, same caps, `SUBMISSION_MODELS` switch only. Runs:
duo `20260823T003216Z`, solo-qwen `20260823T011539Z`,
solo-gptoss `20260823T022516Z`. Scorable ceiling is 14/16.

| arm | solved | spend | notes |
| --- | --- | --- | --- |
| duo | **9/16** | $0.16 | qwen-fast S1 took putnam_2018_a1; S0.5+decide took p06/p07; 1 ledger death (putnam_2020_a2, gpt-oss 429) |
| solo-qwen | 8/16 | $0.45 | missed both Putnams (sampling variance vs duo's qwen wave); most spend of any arm |
| solo-gptoss | 8/16 | $0.04 | missed p07 (answer gate with itself agreed on a wrong path); cheapest by 10×; 1 ledger death (same problem) |

Readings: (1) the duo equals the *union* of the solo arms in one run —
portfolio coverage is real: the solos fail different problems
(qwen missed the Putnams, gptoss missed p07); (2) the cascade means the duo
is also cheap ($0.16) because gpt-oss only engages where qwen fails;
(3) every arm passed exactly the S0 six + its model-specific extras — at
30-min caps the hard tier is out of reach for all arms; (4) `models_used`
shows both models on 9/16 duo problems (the cascade skips gpt-oss when qwen
or tactics already won — participation by design, not by quota).

## 2026-08-23 · Hard-tier at 60-min caps (v2 agent): transport mortality

Run `20260823T033354Z` (p09, p10, rmo_2000_2, rmo_2001_2): **0/4, $0.09** —
but the story is the *why*:

- Three problems died `cost_unknown` to **gpt-oss channel transport
  failures**: one upstream 502, two truncated/malformed response bodies
  (JSON parse failure inside the harness client). Two container restarts of
  the dev environment compounded one of them. qwen's channel had **zero**
  transport kills across every run tonight.
- rmo_2001_2 survived its full 60-min window and exercised the complete
  cross-model S4 flow: gpt-oss sketched a 2-hole decomposition, qwen
  repaired the skeleton to compiling, the cascade filled one hole, and the
  run timed out on the last hole. The machinery works; it needs either more
  time or fewer wasted windows.
- Design response (v3): gpt-oss's S1 wave defers to cycle 2 on long-cap duo
  runs, and `SUBMISSION_GPTOSS_CALL_CAP` (default 10) bounds per-problem
  exposure to the risky channel. Rerun in progress.

Caveat for interpreting all dev-container numbers: tonight's gpt-oss
transport failures may be time-of-day/pool-specific and may differ in the
judging environment; the mitigations are cheap insurance either way.

## 2026-08-23 · Hard-tier at 60-min caps, v3 agent (deferral + call cap)

Run `20260823T065723Z`, same four problems: **0/4 solved — but zero ledger
deaths** (v2: three of four killed). All four problems used their full
~43-minute agent windows, ran S1 both waves, and iterated S4 through up to
three sketch rounds each, ending on compiling qwen-repaired skeletons with
1–2 unfilled holes ($0.04–0.06 per problem). Verdict:

- The v3 mitigations (gpt-oss S1 wave deferred to cycle 2; per-problem
  gpt-oss call cap) eliminated transport mortality in this run while keeping
  both models engaged.
- The hard tier is now a capability×time problem, not a reliability one:
  reference proofs show these four are provable with exactly the lemma
  structures S4 is producing skeletons for; the fills need the real 8-hour
  window (or a stronger per-hole loop) rather than the ~15–25 minutes S4
  got here after S1.

Cumulative dev spend across calibration + five runs: ≈ $0.95 of the $50 key.

## 2026-08-23 · v5 fill loop and the first hard-tier solve

After a direct-read research pass over Delta Prover, APOLLO, MechMath, DSP+
and Prover Agent (fill-stage specifics), v5 rebuilt the hole-filling loop:
depth-first repair dialogues seeded from the best failure (failed script +
located errors in the prompt), model handoff on error-signature plateau,
MechMath-style sorrify salvage of failed scaffolding, Delta-style unsolved-
subgoal feedback into re-sketches, DSP+ granularity prompts, and APOLLO
chained cascade entries. (A first v4 attempt was lost to a Docker/container-
restart race — $0.002, diagnosed, launches now bootstrap-check.)

Hard4 at 2-h caps with v5 (run `20260823T142958Z`): **1/4 —
`p10_factorial_pow` comparator-PASSED** ($0.0497, 64 min) via sketch round 3
→ qwen-repaired skeleton → depth-first fills closing every hole. First
hard-tier solve by the model pair across all baselines and agent versions.
p09 and rmo_2001_2 died `cost_unknown` to gpt-oss sketch-call transport
kills (every ledger death in every run remains gpt-oss-channel);
rmo_2000_2 iterated its full 99-min window without closing.

v6 (committed): qwen is now the primary sketcher — its skeleton produced the
solve while gpt-oss sketch calls produced the deaths; gpt-oss alternates in
from round 2 and keeps its S1/answer-gate/fill-escalation roles.

## 2026-08-23 · Arms seed-2 (matched 30-min caps): duo leads both seeds

| arm | seed-1 | seed-2 | spend (s1/s2) |
| --- | --- | --- | --- |
| duo | 9/16 | **10/16** | $0.16 / $0.17 |
| solo-qwen | 8/16 | 9/16 | $0.45 / $0.40 |
| solo-gptoss | 8/16 | 9/16 | $0.04 / $0.01 |

Runs: duo2 `20260823T162449Z`, qwen2 `20260823T171620Z`,
gptoss2 `20260823T194338Z`. Seed-2 was run with the v5/v6 agent.

Readings: (1) **the duo beats the best solo by +1 on both seeds** at
one-half to one-third of solo-qwen's cost; (2) seed-to-seed variance is
+1 for every arm (better provider health in seed-2); (3) **solo-qwen seed-2
solved p10_factorial_pow at a 30-minute cap** via the v5/v6 sketch/fill
loop — the hard-tier breakthrough reproduced, in a solo arm, at short caps
(duo2's attempt on p10 died to a gpt-oss ledger kill instead: coordination's
one cost is exposure to the risky channel, cured by the upstream kit fix
when it lands); (4) ledger-mortality census across all eight runs: every
death is gpt-oss-channel; solo-qwen arms have lost zero ledgers ever.
Six-run union: 11 distinct problems solved.

At matched 30-min caps: duo 9/16 > solo-best 8/16, duo = union of solos at
one-third of solo-qwen's cost. Baseline comparison: the kit's single-model
25-turn loops scored 7/16 (qwen) and 8/16 (gpt-oss) under comparable
wall-clock; the coordination layer's edge at short caps comes from S0 (6
free), the S0.5 answer gate (p06+p07 solved for ~$0.005 total), portfolio
coverage in S1, and the cascade's cost discipline. The hard tier requires
full-cap runs: next validations are a full-sample run at judge settings
(VM_TIME_LIMIT_S=28800), a real-key `judge_check.sh`, and the Part-2
writeup from these arms.

## 2026-08-23 · Kit fix mirrored ahead of merge; full-cap validation

The upstream kit PRs (#3 `allow_fallbacks` under `max_price`, #5 release
the ledger on zero-cost HTTP refusals) were approved by the maintainer but
still unmerged. Judging clones **our** repo, so waiting gains nothing:
mirrored the approved semantics into `src/re_harness/llm.py` (details:
RESEARCH.md §1.3 update note; tests updated in `tests/test_llm.py`, suite
37 passed / 4 docker-skips). Every 429/502 refusal that killed a ledger in
the eight runs above becomes a wasted sample the v5 agent already absorbs;
mid-flight transport failures and malformed 200s stay fatal by design, so
the agent's pacing/call-cap insurance stays.

Also scaled the agent's anytime-loop cycle cap with the window
(`max(8, agent_time/1500)`): eight cycles fill 30–120 min runs (behavior
unchanged there) but would have stranded ~5 h at the judge's 8-hour cap.

Launched with these in place: **hard4 at full judge caps**
(`VM_TIME_LIMIT_S=28800 VM_BUDGET_USD=1.00`, duo, 4 workers,
`SUBMISSION_GPTOSS_CALL_CAP=24`) — the first run at exactly the judged
time/budget settings. Results appended here when it lands.

## 2026-08-26 · p10 converted: precheck validated end-to-end

Dedicated p10 run (`20260826T062410Z`, 2 h cap, 1 worker): **comparator
PASS, 1/1**, $0.029, 38 min. The winning proof (gpt-oss S1 sample)
cleared the in-run comparator precheck in 97 s and the final comparator
in 45 s. p10 had lost three straight runs to REPL-accepted proofs that
timed out the comparator's cold build; with the precheck the class is
closed in both directions — reject-and-rehunt (p09's two saves) and
confirm-and-ship (here). Full loop history: `RESEARCH_LOOP.md`.

## 2026-08-26 · Full-cap re-validation #2: 1/4, and the precheck earns its keep

Run `20260825T205403Z` (judge caps, duo, reconciled harness + promoted
config + comparator precheck): **1/4**, $2.16, fought through one
container restart and a ~70-min egress outage (openrouter dropped from
the environment allowlist; recovered) with zero ledger deaths across 13
chopped calls.

| problem | this run | first full-cap run |
| --- | --- | --- |
| p09_imo1964 | **PASS** $0.36 / 202 min | PASS $0.098 / 115 min |
| rmo_2000_2 | fail — 5 holes open, $0.89 / 458 min | PASS $0.748 / 444 min |
| rmo_2001_2 | fail — 7 holes open, $0.89 / 460 min | fail (incomplete) |
| p10_factorial_pow | fail — comparator timeout (finished pre-precheck) | fail — comparator timeout |

Readings:

1. **The comparator precheck saved p09's point live.** Its first two
   accepted proofs (a qwen-fast S1 sample, then an S2 repair) were
   REPL-clean but timed out the real comparator at 240 s each — the exact
   class that has now cost p10 three runs. The precheck rejected both,
   the search continued, and the third proof passed the actual gate in
   52 s. Under the pre-precheck code this run scores 0/4.
2. **p09 is now 2-for-2 at judge caps.** rmo_2000_2 is 1-for-2: its pass
   needed a full uninterrupted 7.4 h window, and this attempt was split
   across three segments by the environment — durable state preserves
   lemmas and cycle counts but not in-flight fill context, a
   dev-environment tax judging does not pay. Hard-tier scoring at full
   caps carries real seed variance either way; PART2.md notes it.
3. Both misses ended as credible skeletons (rmo_2000_2's decomposition
   matches the reference proof's structure: bound, then case bash) with
   fills unclosed — capability, not scaffolding, is the binding edge.

The kit merged the official ledger fix (upstream #6). Compared with our
interim mirror it is narrower and more honest: only a **429** is lenient —
released when the refusal reports no cost, **settled at the reported
cost** when it does — while 402/408/5xx stay fatal; `allow_fallbacks`
under the price ceiling is confirmed; `usage.cost` parsing is stricter.
We adopted upstream's `llm.py` and test suite verbatim (50 passed), the
one retained delta being the dev-only `VM_TRANSPORT_FAILURE_POLICY`
knob. Practical consequence: 502s and truncated bodies remain
ledger-fatal at judge settings, so the agent's gpt-oss pacing and call
caps stay load-bearing.

## 2026-08-24 · Dev-container restart storms; durable agent state

The full-cap run surfaced a new dominant hazard, unrelated to providers:
web-container restarts every ~20–60 min. Forensics on run `20260823T230042Z`
segment 1: five `RemoteProtocolError`s at literally the same second
(23:06:51) across three problems — the restart chopping every in-flight
connection — three ledgers closed. (A first attempt `225408Z` had died to
dockerd being down at launch: 0/4, $0.0025.) Two responses, both inert at
judging:

1. `VM_TRANSPORT_FAILURE_POLICY=release` (dev-only env knob, default
   unchanged): transport drops release their reservation. Validated in
   segment 2 — the next restart (00:13:31) chopped nine in-flight calls and
   **all nine released, zero ledger deaths**.
2. Durable per-problem agent state (`agent_state.json` via a new
   `Services.state_dir`): resumed segments skip completed S0/S0.5, keep
   pinned answers, harvested lemmas, failure history, and the cycle count.
   Before this, every ~40-min segment burned its first ~15 min redoing the
   deterministic sweep and re-deferring gpt-oss to "cycle 2" forever; now
   segments compose into one cumulative 8-hour search. Judge runs are
   single-segment: they write the state and never read it.

Resume also grants each segment the full window (`worker.py` builds a fresh
ledger and clock), so wall-clock stretches with each restart; per-segment
events remain the accounting record, and real spend lives in the OpenRouter
dashboard.

## 2026-08-24 · Full-cap validation complete: 2/4, two first-ever solves

Run `20260823T230042Z` finished at 08:01Z: **2/4 at exact judge settings**
(`VM_TIME_LIMIT_S=28800 VM_BUDGET_USD=1.00`, duo, v6 agent + durable
state), $1.86 total spend, 7.7 h wall for the final segment.

| problem | outcome | spend | wall | origin |
| --- | --- | --- | --- | --- |
| p09_imo1964 | **comparator PASS** | $0.098 | 115 min | `gptoss:s4-skeleton:r1:filled` |
| rmo_2000_2 | **comparator PASS** | $0.748 | 444 min | S4 sketch/fill (late cycle) |
| p10_factorial_pow | REPL-accepted, **comparator timeout** (180 s) | $0.211 | 105 min | `sketch:qwen-think:2:filled` |
| rmo_2001_2 | honest incomplete (3 unfilled holes) | $0.805 | 460 min | `sketch:qwen-think:2:partial` |

Readings:

1. **Both passes are first-evers** for the model pair across every run and
   baseline. rmo_2000_2 needed 7.4 h and 75 % of the dollar cap — direct
   validation of the §7 hypothesis that the hard tier is a capability×time
   problem: the same machinery that plateaued at 30–120 min caps closes it
   with the real window.
2. **p09 is genuine duo evidence at judge settings**: the winning skeleton
   came from gpt-oss in the round-robin alternation (qwen sketches first
   under v6; gpt-oss's turn produced the decomposition that filled). A solo
   qwen arm would not have had that sketch.
3. **New failure mode, now guarded**: p10's proof was REPL-accepted but the
   comparator's cold 180 s build timed out — kernel cost that REPL
   acceptance cannot screen (p10 has two comparator passes in earlier runs,
   so it is proof-instance-specific). The agent now records per-check wall
   time (`Candidate.check_s`) and defers any accepted proof that needed
   >40 s in the warm REPL, holding it as fallback while hunting a lighter
   proof whenever ≥30 min of window remain.
4. **Reliability stack held**: after two early restart-killed segments, the
   final segment ran 7.7 h uninterrupted; the one mid-run provider drop (a
   gpt-oss `ReadError` at 02:50) was released under
   `VM_TRANSPORT_FAILURE_POLICY=release` and cost one sample, not a ledger.
   Zero `cost_unknown` outcomes; both ledgers accounting-complete.
5. rmo_2001_2 remains the only provable hard problem the pair has never
   closed (reference proof exists); it burned its full window productively
   (2708-check Lean traffic on rmo_2000_2 vs. a comparable count there) but
   two subgoals never yielded.

Cumulative: the pair has now comparator-passed **3 of the 4 provable
hard-tier problems** somewhere (p09 and rmo_2000_2 at full caps here, p10
at 2 h and 30 min caps in earlier runs). Demonstrated coverage across all
runs: 13 of the 14 scorable sample problems. Cumulative dev spend ≈ $3.7
of the $50 key.

## 2026-08-26 (evening): Phase-2 branch funnel (ten mechanisms, one night)

Ten independently-implemented mechanisms (built by parallel worktree
subagents, merged behind default-off flags, suite 195-passed) were each
evaluated single-flag on the dev-16 at 20-min/$1 caps, serialized through
one 4-worker eval at a time (~45 min, $0.17–0.26 each):

| flag | run | score |
| --- | --- | --- |
| B1 wave-spread | `20260826T144557Z` | 9/16 |
| B5 premise-hints | `20260826T153552Z` | 13/16 |
| B6 suggest-harvest | `20260826T161532Z` | 11/16 |
| B2 plan-first | `20260826T165906Z` | 11/16 |
| B9 skeleton-portfolio | `20260826T174144Z` | 11/16 |
| B10 bound-templates | `20260826T182346Z` | 12/16 |
| B3 cluster-repair | `20260826T190301Z` | 11/16 (mechanism never fired) |
| B4 typed-fills | `20260826T194007Z` | 11/16 |
| B7 strengthen-IH | `20260826T202214Z` | 11/16 (fired once; one infra loss) |
| B8 critic-notes | `20260826T210416Z` | 12/16 |
| B5 confirmation seed | `20260826T214916Z` | 10/16 → **not confirmed** |

Verdict (full composition analysis in `RESEARCH_LOOP.md`): the tuned
defaults are a local optimum; observed spread is flipper churn inside the
±2 noise band; the three structural opens survived everything; prompt-
lengthening mechanisms cost more and scored no better. One environment
note: a container restart mid-B10 was resumed cleanly (`--resume latest`),
and B7's m02 loss was a transport-drop cascade released under the dev
knob, not a capability miss. Phase-2 eval spend ≈ $2.3. Cumulative key
spend ≈ $10 of $50.

B12 (60-min caps, kit hard4, `SUBMISSION_SKELETON_KEEP=1`) launched
`20260826T222901Z` as the long-window transfer check — results below when
scored.
