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
