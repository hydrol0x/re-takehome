# Runbook — local keyed runs

Everything here needs the OpenRouter key (in `.env`, never committed) and
Docker. Costs cited are per full sample-set run and are rough upper bounds;
observed baseline spend was far lower.

## 0. One-time

```bash
bash scripts/setup.sh
cp .env.example .env        # add OPENROUTER_API_KEY=...
bash scripts/smoke_test.sh  # no key needed
```

## 1. Calibration probes (~$0.10, ~5 min)

```bash
.venv/bin/python scripts/calibrate.py
```

Answers: does qwen thinking engage via `reasoning:{enabled}` (baseline ran
with it off), what do gpt-oss effort levels cost in latency/tokens/dollars
through the harness's pinned provider tier, and do both models return clean
```lean fences. Verify the `answer` column shows 49 and check
`outputs/calibration-*.json`. If qwen shows 0 reasoning tokens with
`enabled: true`, the mapping needs investigating before trusting qwen-think
stages.

## 2. Development runs (short caps)

Iterate at 30-minute caps so mistakes are cheap; hard problems won't solve at
this cap, that's fine — the easy/medium tiers are the signal:

```bash
VM_TIME_LIMIT_S=1800 .venv/bin/python run.py \
  --problems sample-problems --out outputs --n-workers 4
bash scripts/rescore.sh outputs/submission/<timestamp>
```

Expected floor: ≥6/16 (S0 alone achieves that with zero spend; S1/S2 should
add p06/p07 and the Putnams).

## 3. Part-2 arms (matched budget, same scaffold)

```bash
# duo (default)
VM_TIME_LIMIT_S=7200 .venv/bin/python run.py --problems sample-problems --out outputs --n-workers 4
# solo arms
SUBMISSION_MODELS=qwen   VM_TIME_LIMIT_S=7200 .venv/bin/python run.py --problems sample-problems --out outputs --n-workers 4
SUBMISSION_MODELS=gptoss VM_TIME_LIMIT_S=7200 .venv/bin/python run.py --problems sample-problems --out outputs --n-workers 4
```

Each run lands in its own timestamped directory; `run.json` records nothing
about the arm, so note the mapping (or export `SUBMISSION_MODELS` visibly in
the shell history). Rescore each, then compare `summary.json`s: solves,
per-problem origin (in `result.json.agent_metadata.origin` — which stage and
model produced the accepted proof), spend, wall time.

Ablations when budget allows: `SUBMISSION_REPAIR_ROUNDS=0` (no repair/handoff),
`SUBMISSION_SKETCH_ROUNDS=0` (no decomposition).

## 4. Final validation (before submitting)

```bash
bash scripts/judge_check.sh          # the judging contract, with the real key
# full-cap run on the stubborn tail only if needed (8h/problem):
VM_TIME_LIMIT_S=28800 .venv/bin/python run.py --problems sample-problems --out outputs --n-workers 4
```

## Budget ledger (dev key $50)

| item | est. cost |
| --- | --- |
| calibration | ~$0.10 |
| dev run, 30-min cap | ~$0.5–2 |
| arm run, 2h cap | ~$1–4 |
| full-cap run | ~$2–8 |

Track actuals in each run's `summary.json` (`actual_cost_usd`) and on the
OpenRouter dashboard. Known ceiling to respect: one problem may never exceed
$1.00 spend — the harness reserves conservatively and the agent stops on
`BudgetExceeded`, but watch the first keyed runs.

## Known sample-set facts (don't chase ghosts)

- **The true mechanical ceiling is 14/16.** `rmo_2000_6` is unprovable as
  formalized (statement false) and `rmo_2000_3` is unscorable (its challenge
  file fails to build under the Comparator — missing `Ico` import). Every arm
  scores 0 on both; see `reference/README.md`.
- Comparator-verified reference proofs exist for p09, p10, rmo_2000_2,
  rmo_2001_2 (plus a REPL-verified rmo_2000_3 proof) in `reference/` — if an
  arm solves the four scorable ones, the pipeline is genuinely working.
