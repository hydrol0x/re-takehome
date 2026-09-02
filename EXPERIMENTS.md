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

B12 (60-min caps, kit hard4, `SUBMISSION_SKELETON_KEEP=1`,
`20260826T222901Z`): **0/4, $0.221** — zero REPL-accepted candidates on
any problem, matching the prior 0/4 defaults run at these caps. Skeleton
persistence buys nothing at 60 min; the hard tier converts only at full
8 h caps, where the coordination layer has already demonstrated p09
2-for-2, rmo_2000_2 1-for-2, and the p10 conversion. Funnel complete.
Phase-2 total spend ≈ $2.8; cumulative key spend ≈ $10.6 of $50.

## 2026-08-29: Full-cap validation #3 (8 h / $1, duo, kit hard4)

Run `20260828T214733Z`, the roughest environment weather of the three
full-cap runs — the gpt-oss channel refused (429) essentially all night,
so the duo ran as de-facto solo-qwen. Score **1/4** (vs #1 2/4, #2 1/4):

| problem | outcome | spend | note |
| --- | --- | --- | --- |
| p09_imo1964 | **comparator PASS, 3-for-3 at full caps** | $0.910 | precheck rejected a kernel-heavy accepted proof at 4h13 (240 s timeout — a would-be scoring zero); agent hunted 5.6 h more and returned a light proof (comparator 46.6 s). Third consecutive run the precheck converts p09 from 0 to 1 |
| p10_factorial_pow | failed | $0.119 | early gptoss-429 storm degraded it to solo-qwen, then its warm REPL died (import timeout ×2) and the bail rail returned a partial at 1h19 |
| rmo_2000_2 | failed | $0.598 | cycle cap (calibrated for ~25-min mixed cycles) hit at 18 fast all-qwen cycles = 4.9 h, stranding 3 h of window on the problem whose only pass took 7.4 h. Fixed post-hoc: past the cap the loop now keeps cycling while ≥45 min of window remains (suite 195 green) |
| rmo_2001_2 | failed | $0.954 | honest incomplete; still the one provable hard problem never closed |

Cross-run hard-tier tally: p09 3/3, p10 1 pass (30-min-cap era), rmo_2000_2
1 pass (7.4 h uninterrupted window), rmo_2001_2 0. The run's lesson is not
capability but robustness bookkeeping: all three losses trace to
environment weather (provider outage, container REPL death) or a cap
mis-calibrated for outage conditions — now corrected. Cumulative key
spend ≈ $13.3 of $50.

## 2026-08-29: Extended experiments (post-funnel, user-requested)

**E1 — scaling-curve point, dev-16 at 40-min caps** (`20260829T052916Z`,
$0.244, cycle-cap fix active): **11/16** — doubling the window did not
move the dev set. Structural opens h02/h04/m06 still unsolved (h02 was
additionally lost to a malformed HTTP-200 body — truncated JSON from the
provider, correctly fatal under the kit's fail-closed accounting — so its
cell is infra, not capability; capability read ≈ 11–12, inside the 20-min
band of 11–13). Flippers: c03/m01 held, h05/h01 lost. Reading: on this
problem mix the 20→40 min curve is FLAT — the marginal minutes go into
more cycles of the same search, and what blocks the opens is structure,
not iteration count. Consistent with the kit hard-tier evidence, where
wins came at multi-hour horizons via accumulated lemma pools rather than
at 2× short windows.

**E2 — structural opens at 2 h caps** (`20260829T063044Z`, h02/h04/m06
only, one worker each, $0.59): **1/3 — h04_square_shift comparator PASS,
a FIRST-EVER.** The problem that survived all ~19 short-window evals fell
with 6× the window ($0.159, comparator 43.1 s). The win doubles as a
design validation: the accepted proof (qwen S2 repair, round 4) was
*precheck-rejected* — the 240 s precheck comparator timed out while all
three workers loaded the box — but the stash-don't-discard fallback
returned it at finalize and the real comparator passed it in 43 s. Two
lessons recorded: (1) capability×time is real on the custom set, not
just the kit set — the structural opens are long-horizon problems, not
unsolvable ones; (2) a precheck timeout under heavy box load is not
proof-weight evidence — the fallback posture, not a discard, is what
made the save cut both ways. h02 ($0.194) and m06 ($0.237) ran full
honest windows without closing. Note: the gpt-oss channel refused (429)
through this run too — every gptoss-med wave came back unusable — so
these are effectively solo-qwen results.

**E3 long-horizon arms (4 h caps).** (c) p10 duo retry
(`20260829T081351Z`): failed at 59 min, $0.096 — but two notable facts:
the **gpt-oss channel recovered** mid-run (its S4 skeleton was
REPL-accepted at 08:36, first useful gpt-oss output after ~12 h of 429s),
and both comparator prechecks timed out at 240 s under 4-worker box load,
exhausting the per-problem precheck budget so the final filled skeleton
shipped unvetted and timed out at scoring. On this shared box a precheck
timeout cannot distinguish a kernel-heavy proof from a loaded machine —
at judge conditions (dedicated resources per worker) the precheck verdict
is meaningful; here it is confounded. p10 remains 1-for-many, its one
pass standing. (b) rmo_2001_2 attempt 1 (`20260829T081343Z`): REPL
Mathlib-import timeout ×2 under load killed it at 53 min with a 10-hole
sketch 5 filled; resumed solo (same run dir, skeleton preserved) once
box load dropped.

**E3b — rmo_2001_2 assault** (`20260829T081343Z`, duo + skeleton-keep +
fill-reasoning, resumed twice across a REPL-contention death and a
container restart; ~4 h total agent time, $0.421): **failed, but the
closest approach yet** — the kept skeleton ended at **one unfilled hole**
(`forward_distinct_primes`), against the historical best of two
never-closed subgoals. Skeleton persistence did its job across three
segments (10 holes → 5 → 1); the last hole — that a solution's p and q
are distinct primes — resisted every fill wave. gpt-oss refused (429)
through this run as well, so the assault ran solo-qwen. rmo_2001_2
remains the one provable hard problem never closed.

**E3a — solo-qwen long-horizon arm** (`20260829T081330Z`, 4 h caps,
p09 + rmo_2000_2, $1.03, resumed once across a container restart):
**1/2 — solo-qwen PASSED p09** ($0.541, comparator 36.9 s). The arc
mirrors the duo's: a kernel-heavy skeleton proof was precheck-rejected
(timed out) at 12:03, the arm kept hunting, and a lighter filled variant
of the same skeleton was accepted at 14:18 and passed the real gate.
rmo_2000_2 failed at 4 h (the duo's one pass needed 7.4 h — horizon
caveat, not a clean comparison). Reading, stated honestly: **at long
horizons the scaffold is the main carrier** — the verifier-centric
ladder + comparator precheck + stash-don't-discard fallback converts p09
in a solo arm too. The duo's measured edges are what they always were:
+1 over the best solo on both matched-budget seeds, union coverage in
one run, one-half to one-third the cost of solo-qwen, one skeleton
(p09 full-cap #1) that only gpt-oss produced — plus, newly visible this
week, **robustness**: gpt-oss's channel refused for ~14 h straight, a
weather event that would have zeroed a solo-gptoss submission entirely
while the duo degraded gracefully to solo-qwen behavior.

**Extended-experiments totals.** Five experiments (~$2.6): one first-ever
solve (h04 at 2 h), one flat scaling curve (dev-16 at 20 vs 40 min), one
solo long-horizon pass (p09) with the scaffold credited, rmo_2001_2
narrowed to a single unfilled hole, and a fixed cycle-cap bug found by
the runs themselves. Cumulative key spend ≈ $16 of $50. Cross-run
hard-tier tally: p09 duo 3/3 + solo-qwen 1/1 at ≥4 h; p10 1 pass;
rmo_2000_2 1 pass (7.4 h); rmo_2001_2 0, best distance 1 hole.

## 2026-08-30 late: raw GPT-OSS baseline (30-min caps) — provider confound and rerun plan

Run `outputs/baseline/20260830T220717Z` (BASELINE_MODEL=openai/gpt-oss-120b,
30-min caps, 4 workers, sample-problems). Two confounds discovered while it ran:

1. **Usage-less provider responses.** Starting 22:32:13Z, OpenRouter
   intermittently routed in-flight calls to DeepInfra, which returned
   HTTP-success completions with no `usage` object; by run end **eight** of
   the sixteen problems (p09, p10, both Putnams, all four RMO problems) had
   been killed this way. The harness's fail-closed accounting
   correctly raises `LLMCallError` ("OpenRouter response omitted required
   usage accounting"), which terminates the reference baseline agent, so all
   five results are `cost_unknown`, not genuine attempts. A direct probe at
   22:45Z routed to Amazon Bedrock with full usage — the fault is
   provider-specific and transient.
2. **Statement revision skew.** This run started after upstream PR #9 was
   adopted, so it saw the revised putnam_2018_a1 / putnam_2020_a2 /
   rmo_2000_6 statements, while every number in the paper's Figure 2
   (including the raw-Qwen 9/16 rerun at 20:17Z) is pre-revision.

Final run-A scoring: clean results only for p01–p08 (7 passed, p08
failed); the other eight are `cost_unknown` (usage-killed), not genuine
attempts. Decision: Figure 2's raw-GPT-OSS bar is assembled from
pre-revision statements only — run A's clean p01–p08, plus run B
(`sample-problems-prerev8/`, extracted from git commit 7436c4c: the eight
affected problems, with the Putnams on their original statements).
Post-revision results are reported separately in the revised-problems
section. Any rerun problem that hits the usage fault again is rerun until a
clean attempt completes (attempt counts logged).

### Run B (prerev8 rerun, 20260830T230426Z) and run C

Run B (gpt-oss raw, 30-min caps, pre-revision statements, 4 workers):
**p10_factorial_pow PASSED** ($0.025, 24 min — the first raw-baseline p10
solve; previously one pass in eight 30-minute controller-arm attempts),
**putnam_2018_a1 PASSED** ($0.003, 165 s), **putnam_2020_a2 PASSED**
($0.006, 474 s). Both Putnam solutions are pure definitional/`rfl`
instantiations (solution.lean in the run dir), the same circular route as
every historical Putnam pass — covered by the paper's §5.4 caveat. The
five remaining problems (p09, rmo_2000_2/3/6, rmo_2001_2) ended
`cost_unknown` again — but event inspection shows these were NOT provider
faults: each is a `CancelledError` stamped exactly at wave-start + 1680 s
(the runner's agent deadline), i.e. the runner cancelled an in-flight LLM
call at timeout, which fail-closed accounting labels `cost_unknown`. They
are genuine full-window failures (zero accepted REPL checks in any of
them), distinct from run A's real DeepInfra usage faults (which carried
provider-stamped response bodies and killed agents mid-window). Run C
(`sample-problems-prerev5k`) reran the five anyway for confirmation.

Provisional Fig-2 raw-GPT-OSS tally (pre-revision statements): p01–p07
pass (run A) + p08 fail (run A) + p10, putnam_2018_a1, putnam_2020_a2 pass
(run B) = **10 confirmed passes**, five problems pending clean completion.


### Run C (20260831T000140Z) — final raw-GPT-OSS tally

Run C: 0/5. rmo_2001_2 `agent_timeout` (clean, no call in flight at the
deadline); p09, rmo_2000_2, rmo_2000_3, rmo_2000_6 again full-window
failures ending in deadline `CancelledError` (`cost_unknown` label; zero
accepted checks). Each hard problem therefore has two independent clean
full 28-minute windows (runs B + C) with no accepted proof.

**Final raw GPT-OSS 30-minute tally (pre-revision statements): 10/16.**
Passes: p01–p07 (run A), p10 ($0.025, 24 min), putnam_2018_a1 (165 s),
putnam_2020_a2 (474 s) (run B; both Putnam solutions are `rfl`-circular).
Fails: p08 (run A, genuine repair-loop failure), p09, rmo_2000_2,
rmo_2000_3, rmo_2000_6, rmo_2001_2 (two clean windows each, runs B/C).
Comparison at the same caps: raw Qwen 9/16, solo-qwen arm 8–9, solo-gptoss
arm 8–8, duo 9–10. Paper updated (Fig 2 bar 8→10 with rerun caption, §5.1,
Tables 1–3 notes, limitations, conclusion).
## 2026-08-31: revised-statement runs (upstream PR #9 statements)

All runs: sample-problems-revised3 (putnam_2018_a1 with the explicit 6-pair
set, putnam_2020_a2 = 4^k, rmo_2000_6 IsLeast 10), 30-min/$1 caps,
3 workers, judge-default fail-closed policy except the dev transport knob.

| run | arm | seed | putnam_2018_a1 | putnam_2020_a2 | rmo_2000_6 |
| --- | --- | --- | --- | --- | --- |
| 20260831T010423Z | duo | 1 | ✗ ($0.057, 23m, qwen-only) | ✗ ($0.023, 18m) | ✗ ($0.034, 18m) |
| 20260831T012801Z | duo | 2 | ✗ ($0.049, 20m) | ✗ ($0.023, 20m) | ✗ ($0.054, 18m) |
| 20260831T014844Z | solo-qwen | 1 | ✗ ($0.051, 22m) | ✗ ($0.058, 20m) | ✗ ($0.052, 19m) |
| 20260831T021056Z | solo-qwen | 2 | ✗ ($0.043, 23m) | ✗ ($0.052, 20m) | ✗ ($0.051, 18m) |
| 20260831T023347Z | solo-gptoss | 1 | ✗ ($0.009, 14m) | ✗ ($0.013, 14m) | ✗ ($0.013, 14m) |
| 20260831T024807Z | solo-gptoss | 2 | ✗ ($0.010, 14m) | ✗ ($0.016, 16m) | ✗ ($0.015, 14m) |
| 20260831T030636Z | duo (2 h caps) | — | ✗ ($0.090, 108m, 405 checks) | ✗ ($0.235, 100m, 926 checks) | ✗ ($0.209, 99m, 632 checks) |


A follow-up duo run at 2-hour caps also went 0/3 (deep genuine attempts:
405–926 REPL checks per problem), so the revised problems resist the
controller at the medium horizon too.

**Revised-statement program summary: 0-for-18 at 30 minutes, 0-for-3 at 2 hours** (3 problems × 3 arms × 2
seeds, 30-minute caps, $0.009–0.058 per problem-attempt, every attempt a
genuine 14–23-minute run). With the definitional route eliminated, both
revised Putnams behave as genuine hard-tier instances for every arm, and
the now-provable rmo_2000_6 did not fall at a short horizon either —
consistent with the paper's finding that this tier yields at multi-hour
horizons. Paper §5.4 updated with this result.

### 8-hour full-cap attempts, launch incidents (2026-08-31 ~19:03–19:13Z)

Three aborted launch attempts, all $0 / zero LLM calls, run dirs removed:
one with dockerd down after a container restart (instant 0/3), then both
8h runs (revised3 ×3 workers + rmo_2001_2 ×1, staggered only ~2 min) died
at "REPL failed to import Mathlib: TIMEOUT after 180s" — four concurrent
cold Mathlib imports on a fresh machine. Relaunched revised3 alone (run
20260831T191439Z, healthy: all three REPLs importing then sweeping).
A second rmo_2001_2 attempt at 19:40Z — one cold import against the three
settled-but-CPU-saturated revised3 workers — also failed its import: the
duo agent's S0 sweeps keep the REPLs elaboration-bound, unlike the
baseline agents (model-latency-bound) that coexisted at 4 workers. Plan
changed to strictly serial: rmo_2001_2 launches on the empty machine when
revised3 completes (~03:15Z Sept 1).

### 8-hour duo on the revised statements (20260831T191439Z) — near-solve of rmo_2000_6

| problem | outcome | cost | wall | note |
| --- | --- | --- | --- | --- |
| putnam_2018_a1 | ✗ | $0.770 | 7.7 h | genuine deep miss; 3642 REPL checks, 0 accepted; 2 transient llm_errors absorbed by rails |
| putnam_2020_a2 | ✗ | $0.972 | 6.7 h | **first budget-exhausted problem ever** (stopped by the $1 ledger, not the clock); 2628 checks, 0 accepted |
| rmo_2000_6 | ✗ | $0.092 | 1.4 h | **REPL-accepted proof found** (correct witness (1,10): 1·10⁵=2000·50, 10⁴=2000·5), **twice** — comparator precheck rejected it (31 s, `passed=false`), final scoring confirms: both files build, kernel statement comparison fails: "Challenge and solution theorem statement do not match" |

The rmo_2000_6 outcome is the paper's REPL≠Comparator gap on the *solution*
side: the agent's file adds `import Mathlib.Tactic` (needed for
interval_cases/nlinarith), and the same statement text apparently elaborates
to a different kernel term than under the challenge's two minimal imports.
The in-run precheck caught it exactly as designed. Probes A/B/C (matching
imports + sorry; +Mathlib.Tactic + sorry; full Mathlib + sorry) staged to
pin the mechanism; results below.

### rmo_2000_6 statement-mismatch mechanism: probes + scorability certificate

Probes (comparator, fresh containers; challenge = revised statement):
- **A** solution with the challenge's exact two imports + `sorry` →
  statements **match** (sole failure: `Illegal axiom detected: 'sorryAx'`).
- **B** + `import Mathlib.Tactic` + `sorry` → **"Challenge and solution
  theorem statement do not match"**.
- **C** `import Mathlib` + `sorry` → same mismatch.

So the mismatch is caused entirely by the solution's import surface
changing how the identical statement text elaborates; the agent's
mathematically-correct proof (and any full-Mathlib proof) can never score
on this problem as composed. Constructive resolution: a reference proof
written inside the challenge's import surface — core tactics only, with
`decide`-driven 100-case bounded exhaustion replacing interval_cases —
**passes the Comparator** (`reference/rmo_2000_6_revised.lean`,
passed=True, 14.0 s). The revised-statement scorable ceiling of 15/16 is
therefore certified, and the constraint it imposes on solvers (matching
import surfaces, or a final-composition stage that re-targets the
challenge's imports) is documented as future agent work.

Note: the rmo_2001_2 8-hour run (20260901T025836Z) was interrupted at
4.96 h (2053 events, 13 cycles, populated lemma pool) by a dev-container
restart at ~07:56Z and resumed at 07:58Z with its durable agent state
(`--resume`; fresh worker window per the kit's resume semantics). Total
accumulated wall time will be reported with the final result.

### rmo_2001_2 final 8-hour attempt (20260901T025836Z, resumed)

FAILED — stopped by the agent's own budget rail at $0.893 of $1.00
(cumulative across the interruption; ~4.96 h + 7.69 h ≈ 12.6 h total wall).
29 decomposition cycles, 3519 REPL checks, 0 accepted candidates, 0
prechecks triggered; final best candidate is an S4 sketch with exactly
**one unfilled hole** — the same distance as the 4-hour attempt. rmo_2001_2
remains the one provable kit problem outside cumulative coverage (13/14
scorable under original statements). Paper Table 3 updated.

## 2026-09-01: import-surface fallback (post-audit mechanism), custom-set baselines

Following the rmo_2000_6 near-solve, two generic changes (no per-problem
content), both covered by offline tests and `judge_check` (PASSED 20:14Z):

1. **Composition rule** (`lean_text.guard_candidate`): every candidate is
   composed on the challenge's exact import block. The warm REPL strips
   imports, so this is invisible during search; the Comparator compares
   kernel-level statements, so a model-added `import Mathlib.Tactic` on a
   minimal-import challenge can only hurt. Idempotent on `import Mathlib`
   challenges (all 14 other kit problems, all 24 custom problems).
2. **S5 surface repair** (`SUBMISSION_SURFACE_REPAIR`, default on): when the
   comparator precheck rejects a REPL-accepted winner outright (not a
   timeout) on a challenge narrower than `import Mathlib`, one bounded
   repair round confined to the challenge's imports (core tactics only; a
   lint rejects Mathlib-only tactics before REPL time is spent), then one
   more precheck. Never fires on `import Mathlib` challenges; any failure
   ships the original winner exactly as before. `worker.py`'s precheck now
   returns the comparator's diagnostic tail (`reason`) for this purpose.

Validation planned: duo, 30-min caps, revised rmo_2000_6 (2 seeds) once the
custom-set baselines release the machine.

Surface-repair validation, seed 1 (20260901T201718Z, duo, 30 min, revised
rmo_2000_6): ✗ ($0.034, 18 min) — no REPL-accepted candidate arose, so the
fallback never fired (uninformative for the mechanism; consistent with the
earlier 0/6 at 30-min caps — the precondition first appeared at 75 min in
the 8-hour run). Follow-ups: a 2-hour seed, and a direct offline test of the
confined-repair prompt against both models with the 8-hour run's rejected
proof as feedback, scored by the Comparator.

### Raw Qwen 30-min baseline on the custom 24 (20260901T200131Z)

**12/24** ($0.315 total): dev-16 **8/16** (c01, c02, c06, c08, c10, h05,
m01, m04), held-8 **4/8** (c04, c07, c09, m07). Comparison with the
controller (duo) at *20-minute* caps from RESEARCH_LOOP.md: dev-16 11–13
(band; tuned default), held-8 6/8 on both checks (c04, c07, c09, m03, m07,
h06; missed h03, m05). On the held-out 8 the duo's set is a strict superset
of the raw loop's (+m03_recip9, +h06_order_mod125), with a shorter window;
on dev-16 the duo additionally covers c05, h01, m02, m08 (and the c03/m01
flippers on good seeds). Unlike the kit set, where the raw loops reach
parity, the custom benchmark shows a scaffold gain of +2/8 held and roughly
+3–5/16 dev at a 10-minute cap disadvantage. (gpt-oss raw on the custom 24
running next.)

Surface-repair validation, seed 2 (20260901T203559Z, duo, 2-hour cap,
revised rmo_2000_6): ✗ ($0.025) — but the precondition arose at 12 min this
time and the new path executed end-to-end: precheck rejected the
REPL-accepted winner (not a timeout, 6 s); S5-surface's lint rejected the
first confined candidate for `interval_cases`; the bounded confined round
produced no accepted core-only proof; the agent shipped the original winner
and exited with 108 min of window unused. Diagnosis: plumbing works; the
gap is (i) model capability under the restricted surface in one round, and
(ii) the early exit — after a failed confined round the search should
continue in a surface-aware mode for the remaining window.

Offline confined-repair prompt test (before the technique-block revision):
both models × 3 samples, given the 8-hour run's rejected proof and the
comparator diagnostic, asked for a core-only proof under the challenge's
imports; each sample composed, linted, and scored by the Comparator.
**0/6 passed**; 5/6 were lint-clean core-only attempts that failed to build.
Failure modes: `decide` applied to `∣` goals (no Decidable instance under
these imports) and Mathlib lemma names (`one_pow`) that do not exist in the
closure. The SURFACE_TECHNIQUES block now states both explicitly (quotient
witnesses for `∣`, `obtain`+`omega` for `∣` hypotheses, no Mathlib lemma
names); rerun follows.

Surface mode continuation (code): after a failed confined round the agent
no longer stops — it keeps the REPL-accepted winner as the shipping
fallback and continues the search in surface mode (S1/S2 prompts carry the
import-surface constraint, candidates are linted, precheck cap 4). Tests:
210 passed.

Judge-check failure diagnosis (2026-09-01 ~20:50–21:12Z, machine load 4.6–6.9
on 4 cores with 7–9 Lean containers): a judge-invocation replica on p01 kept
its artifacts. The agent behaved exactly as designed — zero LLM calls, the
$0 S0 sweep solved p01 (`sweep:nlinarith`), and the comparator precheck
PASSED (194 s) — but the runner's final scoring comparator returned
passed=False timed_out=True after 180519 ms: under
saturation, even p01's cold build exceeds the kit's 180 s scoring limit
(the REPL import also timed out once and recovered). The earlier failed
judge_check (cost_unknown) ran under the same load. Neither involves the
code paths changed today (no LLM call occurred); judge_check is re-run on a
quiet machine before submission and must pass there.

Offline confined-repair prompt test, after the technique-block revision:
**0/6 again** (qwen 0/3: one lint-clean build failure with omega gaps, two
lint rejections; gpt-oss 0/3: two lint-clean build failures — `subst`
misuse, unknown `Nat.prime_two`/`Nat.prime_five` — and one lint rejection).
The revision removed the specific earlier failure modes but the models do
not reliably find the bounded-`decide` proof structure that the in-repo
reference uses. Conclusion: the mechanism's plumbing is verified end-to-end
(seed 2 live run), but in one confined round neither model produces a
scoring core-only proof for rmo_2000_6; the composition rule is the robust
gain (it rescues any proof that only added imports gratuitously), and the
confined repair + surface-mode continuation remain a demonstrated fallback
whose effectiveness is bounded by model capability under a restricted
surface. Reported as such in the paper.

judge_check re-run on a quiet machine (load 0.4, 21:20Z Sept 1) with the
full surface-mode code: **PASSED** (score 1/1, $0.00) — the earlier failure
was the load-induced final-scoring timeout diagnosed above.

### Held-8 arms at 30-min caps (RQ2 replication on unseen problems)

| run | arm | held-8 | solved | machine load |
| --- | --- | --- | --- | --- |
| 20260825T174536Z | duo (20-min, earlier check) | 6/8 | c04 c07 c09 m03 m07 h06 | light |
| 20260825T183009Z | duo (20-min, earlier check) | 6/8 | same six | light |
| 20260901T204827Z | duo (30-min) | **4/8** ($0.096) | c04 c09 h06 m07 | **saturated** (load 4.6–6.9: 3 duo + 4 baseline workers + judge replica + comparators); c07 and m03 — solved in both earlier checks — timed out at 18 min |
| 20260901T200131Z | raw Qwen (30-min) | 4/8 ($0.06) | c04 c07 c09 m07 | moderate |
| 20260901T212748Z | solo-qwen (30-min) | **6/8** ($0.165) | c04 c07 c09 h06 m03 m07 (identical to the duo's two 6/8 checks) | light (baseline only, load ≈0.5–1.5) |
| 20260901T220258Z | solo-gptoss (30-min) | 5/8 ($0.066) | c04 c07 c09 h06 m07 | light (baseline only) |
| 20260901T223706Z | **duo rerun (30-min)** | **7/8** ($0.144) | c04 c07 c09 h03 h06 m03 m07 — **h03_invsq_sum first-ever solve** (winning proof: a qwen-fast S1 sample in a later cycle after S4/S2 rounds; 88 Qwen / 3 GPT-OSS calls; precheck passed in 40 s) | light (baseline only, matched with the solo arms) |
| 20260902T075141Z | duo, seed 2 (30-min, light load) | 6/8 ($0.091) | c04 c07 c09 h06 m03 m07 (same set as solo-qwen; h03 and m05 missed) | light (idle machine) |

Cross-run duo tally on held-8 (five runs): c04 5/5, c09 5/5, m07 5/5, h06
5/5, c07 4/5, m03 4/5, h03 1/5, m05 0/5. Under matched light load at 30-min
caps the ordering is duo 7/8 > solo-qwen 6/8 > solo-gptoss 5/8 > raw Qwen
4/8; the duo's extra problem (h03) was a Qwen-wave coverage event, not a
cross-model artifact — consistent with the paper's scaffold-then-coverage
reading. The duo covers two problems the raw loop did
not (m03, h06; 2–3 of 3 runs each); both miss h03/m05. The 30-min duo run
is load-confounded and is rerun on a quiet machine after the baseline
finishes, so that all three 30-min arms are compared under comparable
conditions; solo-qwen and solo-gptoss arms follow with only the light
gpt-oss baseline in the background.

### Raw GPT-OSS 30-min baseline on the custom 24 — first run invalid (20260901T203834Z)

6/24 nominal, but 10 problems ended `harness_error` (the kit's simple
baseline has no rails: "REPL failed to import Mathlib: TIMEOUT after 180s"
at 21:02–21:43Z, plus one transport `ReadError`), one `cost_unknown`, and
the timed-out problems got fewer turns — all inside the day's saturation
window (duo + qwen held-8 arms, judge replica, judge_check, comparators on
4 cores). Treated as load-confounded and rerun in full on a light machine
(only the latency-bound solo-gptoss arm in the background). The first
run's dir is kept for the record; its numbers are not used.

### Raw GPT-OSS custom-24, second run (20260901T221432Z, light load)

Nominal 6/24 ($0.36): passed c04, c08, c09, m02, m07, m08; statuses: 6 passed, 2 failed, **10 `cost_unknown`**, 6
`harness_error`. Event inspection: all 10 `cost_unknown` are the runner's
deadline cancellation of an in-flight call (`CancelledError` at
"agent exceeded 1680.0s"; zero accepted checks) — genuine full-window
failures, the same technicality documented for the kit-set runs. Of the six
`harness_error`s, five are provider transport faults (`RemoteProtocolError:
peer closed connection without sending a complete response` on c03, c05,
c06, c10, m01 — the dev policy released the reservation but the rail-less
baseline still dies) and one is a REPL import timeout (h01). Only those six
are rerun (attempt 3, `custom-problems-gptoss6`); the other 18 results
stand. Note that our controller's rails absorb exactly these faults (the
same provider produced 2 transient errors inside the duo's 8-hour
putnam_2018_a1 attempt without ending it).

Attempt 3 (20260901T235516Z, light load): c05 ✓ (7 m), c06 ✓ (2 m), c10 ✓
(1 m), h01 ✗ (genuine, 23 m), c03 and m01 full-window deadline fails — no
provider faults this time. **Final raw GPT-OSS 30-min custom-24: 9/24**
(dev-16 **6/16**: c05 c06 c08 c10 m02 m08; held-8 **3/8**: c04 c09 m07),
assembled from run 2's 18 valid results + attempt 3. Union of the two raw
loops: 15/24. Controller for comparison: dev-16 11–13 (20-min), held-8 6/8
×2 (20-min) and 7/8 (30-min, matched light load).

Data-count note (2026-09-02): the cap-matched kit-set record at 30-min caps
is nine full 16-problem runs — duo 20260823T003216Z (9), 20260823T162449Z
(10), 20260825T192220Z (9, $0.34; post-promotion check, previously
unlabeled here); solo-qwen 20260823T011539Z (8), 20260823T171620Z (9);
solo-gptoss 20260823T022516Z (8), 20260823T194338Z (9); raw Qwen
20260830T201716Z (9); raw GPT-OSS (10, assembled from runs A/B/C). Figure 2
now shows all seven controller runs and both raw loops.

### Long-horizon raw-loop control: structurally unavailable (2026-09-02)

The kit's reference baseline is hard-capped at 25 turns (`BASELINE_MAX_TURNS`,
maximum 25), so it cannot use a long window. In the 30-minute raw runs Qwen
already exhausted all 25 turns on rmo_2000_2 (13 min) and rmo_2001_2
(25 min) and solved p09 at turn 11; GPT-OSS, latency-bound, completed
11–22 turns before the 30-minute deadline. An "8-hour raw run" therefore
adds nothing for Qwen and at most 3–14 turns for GPT-OSS. Consequence for
the paper: the controller's long-horizon solves (p09 3/3 at 8 h,
rmo_2000_2 at 7.4 h, p10/h04 at 2 h) lie outside anything the raw loop can
attempt as shipped, and no like-for-like raw control at long horizons
exists. A GPT-OSS raw run at an 8-hour cap on p09 and rmo_2000_2 (letting
it finish its 25 turns) is queued behind the dialogue screening.

## 2026-09-02 night program (self-paced loop)

Queue: D1 dialogue repair (running) → D2 plan dialogue → D1+D2 → same-day
default control (all dev-16, 20-min caps, 4 workers); alongside: raw GPT-OSS
at its full 25-turn budget under an 8-hour cap on p09 + rmo_2000_2 (the
30-minute runs truncated it at 11–14 turns). Then: a second light-load duo
seed on held-8; SUBMISSION_SKELETON_KEEP at 2-hour caps on the kit hard4
(untested at any horizon beyond 20 min); solo-qwen at 8-hour caps on hard4
(RQ3 attribution: is the long-horizon record duo-specific?).

### Dialogue mechanisms (D1/D2), dev-16 at 20-min caps, 4 workers

| run | mechanism | dev-16 | cost | notes |
| --- | --- | --- | --- | --- |
| 20260902T024814Z | D1 dialogue repair (other model reviews each failing attempt; author repairs with errors + review) | **9/16** ($0.218) | 283 Qwen / 13 GPT-OSS calls | review fired 7× across 4 problems only — a GPT-OSS review costs minutes at this cap, so most repair rounds never reach it and those that do lose cycles; missed c03, c10, h01, h02, h04, h05, m06 (band: 11–13; B8 one-way critique: 12) |
| 20260902T033213Z | D2 plan dialogue (propose → other model critiques → sketch), 20-min caps | 10/16 ($0.211) | 340 Qwen / 5 GPT-OSS calls | **mechanism never fired**: the S4 time gate (critique + two sketch calls + slack) never clears inside a 20-min window, so this run is a default-equivalent datapoint (band 11–13). Rerun at 40-min caps, where S4 has room (default at 40 min: 11/16) |
| 20260902T041411Z | D2 at 40-min caps, original gate | 9/16 ($0.373; m02 invalid — REPL import timeout) | S4 reached in 9 problems, **0 exchanges** | the gate (worst-case GPT-OSS timeout + two sketch calls + slack) never clears even at 40 min; effectively a default run at 40-min caps under moderate load (earlier default at 40 min: 11/16). Gates re-sized on typical review duration; rerun follows |
| 20260902T053118Z | **D2 plan dialogue at 40-min caps, working gate** | **12/16** ($0.375) | 17 exchanges across 10 problems (all 10 that reached S4); 493 Qwen / 34 GPT-OSS calls | inside the band (40-min default: 11; 20-min band 11–13); the structural three (h02, h04, m06) still missed, plus m02; ≈+50% cost over a default 40-min run. Reads as neutral: the critiques are substantive (e.g. rejecting a norm_num plan for 2^2025 in favour of Int.ModEq.pow) but do not convert any problem the default misses |
| 20260902T064728Z | **D1 dialogue repair at 40-min caps, working gate** | 10/16 ($0.357) | 24 reviews across 7 problems; 396 Qwen / 41 GPT-OSS calls | at the low edge of the band with ≈+45% cost; missed c03, h01, h02, h04, m02, m06 |

### Raw GPT-OSS at its full 25-turn budget, 8-hour cap (20260902T030628Z)

p09: ✗ after all 25 turns (128 min, $0.068, 0 accepted checks).
rmo_2000_2: ✗ through 21 turns (79 min, $0.044, 0 accepted) when a provider
transport fault ended the rail-less loop. Given the whole turn budget the
raw GPT-OSS loop still does not reach either problem; its limit here is the
25-turn cap, not wall-clock, so no long-horizon raw control is possible
with the kit baseline as shipped (see §5.3).

**Dialogue conclusion.** Two genuine two-model exchanges were built and
tested at the screening protocol's caps (20 min, then 40 min so that the
exchanges actually fire): plan dialogue before sketching scored 12/16 with
17 exchanges (band 11–13; prior 40-min default 11), and review-informed
repair scored 10/16 with 24 reviews (9/16 at 20 min where it rarely fired).
The earlier one-way critique (B8) scored 12. None of the three converted a
problem the tuned default misses, and both two-way mechanisms cost 40–50%
more per run. Verdict: neutral at best at short horizons; not promoted.


### Solo-Qwen on the kit hard four at 4-hour caps (20260902T081939Z) — RQ3 attribution

**1/4, $1.36: rmo_2000_2 PASSED** (220 min, $0.484, Qwen only) — the problem
the duo solved once in three 8-hour runs. With the earlier 4-hour solo-Qwen
p09 pass, two of the three multi-hour kit solves reproduce under the same
scaffold with a single model. p09 here produced six REPL-accepted proofs
but both prechecks timed out under four-worker load and final scoring
failed on the same limit (load artifact; quiet rerun queued); p10 hit a
REPL import timeout mid-run (invalid). rmo_2001_2: unsolved (220 min,
$0.52, no accepted candidate), as in every configuration.


### Parallel raw pair: the minimal two-model control arm (`baselines/pair_agent.py`)

The kit-set result that two raw loops' *union* (12/16) beats every controller
run raises the obvious question: is the union an artifact of adding up two
separate runs, or would the simplest possible coordination, two independent
raw loops under one budget and one window with the verifier picking the
first accepted proof, actually score 12? `baselines/pair_agent.py` is that
arm: the kit's raw loop once per model, run concurrently, byte-identical
prompts, no shared context; the first REPL-accepted candidate wins and the
other loop stops cooperatively (an in-flight call is allowed to finish
because cancelling it would close the shared ledger). `PAIR_RESTARTS=1`
restarts a loop that exhausted its 25 turns while the window allows, which
gives the raw loops a long-horizon form for the first time (independent
restarts). Both forms are controls for the coordination layer: what the
staged controller adds over them is search organization, not two models.


### Skeleton persistence at 2-hour caps on the kit hard four (20260902T120042Z, duo, `SUBMISSION_SKELETON_KEEP=1`)

**1/4, $0.50** (p10 ✓ at 91 min; p09, rmo_2000_2, rmo_2001_2 ✗ with no
REPL-accepted candidate in 101–102 min). p10's pass needed a rescore: its
six REPL-accepted proofs arrived while three other heavy workers were
active, both in-run prechecks timed out (240 s) and the final Comparator
timed out (181 s); on the quiet machine the same solution passes in 59 s
(evaluator rerun; the same load artifact as p09 in the solo-Qwen 4-hour
run). The mechanism itself fired once per problem (a stalled skeleton was
kept and resumed) and converted nothing: p10 falls at short caps without it,
and the other three are the problems that yield only at 4–8 hours (p09,
rmo_2000_2) or never (rmo_2001_2). With the 20-minute dev screen (13 → 12)
and the 60-minute hard-four run (0/4), skeleton persistence is now tested at
three horizons with no gain at any; it stays opt-in.

**Addendum (rescore, 2026-09-02 13:47Z).** The p09 solution from this
solo-Qwen 4-hour run (origin `qwen-fast:s1`, REPL-accepted, final
Comparator timed out at 181 s under four-worker load) **passes the
Comparator in 51 s on the quiet machine** (evaluator rerun, mechanical
re-check of the existing solution). The run is therefore 2/4 on the proof
itself (p09, rmo_2000_2), with the in-window verdict for p09 lost to load:
p09 has now been solved by solo-Qwen at 4 hours in both runs that tried it.

**p10 rerun (20260902T134847Z, solo-Qwen, 2-hour cap, 1 worker, light load).**
Replaces the import-timeout loss above: **PASSED in 14 min, $0.039**, via
an S4 skeleton fill (round 3); precheck 45 s, final Comparator 57 s. p10
remains a short-cap problem under the scaffold for either model set.

#### Pair arm on the kit 16, 30-minute caps, 4 workers (20260902T134450Z, revised statements)

**9/16, $0.46** (p01–p09; per-loop cost of the two raw loops run separately was
$0.24 + $0.21). Winners: Qwen on p01–p04, p06, p08 (turn 1) and p09 (turn 2,
4 min); GPT-OSS on p05 (turn 8) and p07 (turn 4). Unsolved: p10 (Qwen 25
turns, GPT-OSS 6), both Putnams (revised statements, no definitional route),
rmo_2000_2, rmo_2000_3, rmo_2000_6, rmo_2001_2 (`cost_unknown`: a Qwen call
started at 1358 s ran 375 s and was still in flight at the 1680 s agent
deadline; raw calls reach 440–470 s in this run, so the 300 s turn guard was
too short and is raised to 480 s). On revised statements the two raw loops'
union is 10 (p01–p10); one 30-minute window of the pair realizes 9 of those
10 in one budget, level with the controller's 30-minute arms (8–9 on revised
statements) and above them on p09, which no controller arm solved at 30
minutes in seven runs (zero REPL-accepted p09 candidates in all seven),
while the raw Qwen loop is now 2-for-2 on p09 at short caps (11 turns in the
solo raw run, 2 turns here; both proofs pass the Comparator in 26–49 s).

### R1: the kit baseline's loop as a controller stage (`SUBMISSION_RAW_LOOP`)

Why: on p09 the raw Qwen loop is 2-for-2 at 30-minute caps (turn 11 in the
solo raw run, turn 2 in the pair run; both proofs pass the Comparator in
26–49 s), while all seven 30-minute controller runs produced zero
REPL-accepted p09 candidates across 8–20 qwen-fast and 1–21 qwen-think
samples each. The raw calls use no reasoning budget (0 reasoning tokens,
~2–3k completion tokens, 12–16 s), so the difference is not thinking: it is
the request profile (temperature 0.2 vs 0.8), the prompt (the kit's plain
"complete Lean file" system prompt vs the controller's rules + cookbook), and
the loop shape (one chronological whole-file chain fed the previous errors,
vs independent samples then repair rounds). What: `stage1r_rawloop` runs the
baseline's Qwen loop verbatim (prompt and feedback format byte-identical,
unit-tested against `baselines/simple_agent.py`) for up to 8 turns at cycle
1 after the S1 wave, behind the statement guard; an accepted candidate takes
the normal precheck path. Pilot: p09 at 30 min, 2 seeds, alongside two more
raw-Qwen p09 seeds to pin the raw rate; kit-16 at 30 min if positive.

#### Pair arm on the held-out 8, 30-minute caps, 4 workers (20260902T144753Z)

**4/8, $0.22**: c04, c09, m07 (Qwen, turn 1) and h06 (Qwen, turn 18, 9 min).
Unsolved: c07 (the solo raw Qwen run had it), h03, m03, m05. Same total as
the raw Qwen loop alone (4/8) and the raw union (4/8, now 5/8 counting this
seed's h06), below solo-Qwen 6/8, solo-GPT-OSS 5/8 and the duo's 7/8 and
6/8 at the same caps. The held-out scaffold effect therefore survives the
strongest scaffold-free control: two raw loops in one window add nothing
over one on these problems, while the same models inside the controller
add two to three.

**Pair-arm summary.** Kit 16: 9/16 (revised statements), the two raw loops'
union being 10 there; held-out 8: 4/8 against a raw union of 4–5. The union
of separate raw runs overstates what concurrent raw loops deliver, and the
controller's margin on unseen problems is intact. The one thing the pair
did that the controller never did at 30 minutes is p09 (turn 2), which is
now research branch R1.

#### Pair arm on the held-out 8, 30-minute caps, 4 workers (20260902T144753Z)

**4/8, $0.22** (c04, c09, m07 at turn 1; h06 by the Qwen loop at turn 18,
9 min). Unsolved: c07, h03, m03, m05 (Qwen 25 turns each, GPT-OSS 5–8 turns
to the deadline). Level with the raw Qwen loop alone (4/8) and below every
scaffolded arm (solo-GPT-OSS 5, solo-Qwen 6, duo 7 and 6): on unseen
problems the scaffold's margin survives the strongest scaffold-free control.

#### Raw Qwen loop on p09 alone, 30-minute cap (20260902T152550Z, seed A)

**PASSED** at turn 10 ($0.009, 4 min wall, Comparator 52 s). The raw Qwen
loop is now 3-for-3 on p09 at 30-minute caps (turns 11, 2, 10) against
0-for-7 controller runs with zero REPL-accepted p09 candidates. Its calls
carry no reasoning budget (temperature 0.2, ~2–3k completion tokens), so
the difference is prompt and loop shape, not thinking. Research branch R1
(`SUBMISSION_RAW_LOOP`) runs that loop verbatim inside the controller at
cycle 1; p09 pilot (two controller seeds) and a second raw seed follow.

Container-restart note (15:40Z): the session worker restarted and killed
the 4-hour restarts control (hard3k, 18 min in, no accepted candidate) and
the pilot chain after its first run; both relaunched at 15:43Z.

R1 pilot, first attempt (20260902T152944Z, duo + `SUBMISSION_RAW_LOOP=1`,
default 8 turns, killed at 11 min by the worker restart): the stage fired
all 8 turns after the S1 wave with the prompt byte-identical to the raw
loop's (only "turn t/8" vs "t/25" differs), no accepted candidate (error
counts 3, 10, 16, 11, 5, 7, 4, 15). Two of the raw loop's three p09 solves
came at turns 10–11, so the pilot proper runs with
`SUBMISSION_RAW_LOOP_TURNS=16` (relaunched 15:48Z, two controller seeds
interleaved with a second raw seed).
