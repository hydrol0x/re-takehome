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
