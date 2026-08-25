# Research loop — variant selection on the custom eval set

Goal: use the remaining key budget (~$46) and days before the deadline to
improve the coordination agent measurably, with selection pressure from a
wider problem distribution than the 16 kit samples.

## Eval sets

- `custom-problems-dev/` — 16 problems (easy/answer/medium/hard mix),
  authored by frontier-assistant subagents in exact kit format, each with a
  REPL-verified reference proof (truth certificate) and a
  comparator-build-verified pristine challenge. **Selection metric runs
  here.** Reference proofs live outside the repo runtime paths and are
  never read by the agent (same policy as `reference/`).
- `custom-problems-held/` — 8 problems held back from the loop. Run rarely
  (promotion candidates only) to detect overfitting to the dev set.
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
| 0 | 2026-08-24 | baseline v6+guard | (pending first eval) | — | dev-set baseline |
