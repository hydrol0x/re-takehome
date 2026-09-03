# Verified Mechanisms Take-Home Harness

This repository contains the infrastructure for the Verified Mechanisms
research engineer take-home assignment. The applicant is responsible for
implementing an agent in Python. The harness provides the surrounding runtime:
OpenRouter access, per-problem budget accounting, durable logs, concurrent
problem scheduling, Dockerized Lean checking, and final Comparator scoring.

Lean, Mathlib, compiled Mathlib artifacts, the JSON REPL, `lean4export`, and
Comparator are supplied through a pinned Docker image. Applicants do not need a
host Lean, Lake, or Mathlib installation.

## Requirements

- Docker Engine or Docker Desktop
- Python 3.11 or newer
- Approximately 20 GB of free disk space
- At least 8 GB of RAM for one worker

Each additional worker may require roughly 5 GB of additional memory. Linux,
WSL2, Intel Macs, and Apple Silicon Macs are supported.

## Setup

Run the setup script from the repository root:

```bash
bash scripts/setup.sh
```

Create a local environment file and add the OpenRouter API key:

```bash
cp .env.example .env
```

The `.env` file is ignored by Git. During judging, exported environment
variables take precedence over values in `.env`.

## Implementing the Agent

Applicants implement `SubmissionAgent.solve` in `submission/agent.py`.

```python
async def solve(problem: Problem, services: Services) -> AgentResult:
    ...
```

The harness supplies three services:

- `await services.llm.complete(...)` for restricted, budgeted, logged
  OpenRouter calls
- `await services.lean.check_file(source)` for checking a complete Lean file in
  the networkless Lean container
- `services.checkpoint(source)` for preserving a candidate solution during a
  long run

The agent may use any internal design that remains problem-agnostic and follows
the assignment rules. See `docs/AGENT_API.md` for the full interface.

## Running the Harness

Run the default submission agent with:

```bash
.venv/bin/python run.py --problems sample-problems --out outputs
```

Each invocation creates a fresh run directory:

```text
outputs/submission/<run-name>/
```

The run name is generated from the current UTC timestamp.

To resume a previous run for the selected agent:

```bash
.venv/bin/python run.py \
  --problems sample-problems \
  --out outputs \
  --resume latest
```

You may also resume a specific run name:

```bash
.venv/bin/python run.py \
  --problems sample-problems \
  --out outputs \
  --resume 20260819T120000Z
```

## Reference Baseline

A minimal reference agent is available in `baselines/simple_agent.py`. It uses a
single model-driven repair loop with Lean feedback and stops when a candidate
passes the Lean REPL check.

Run it with:

```bash
.venv/bin/python run.py \
  --problems sample-problems \
  --out outputs \
  --agent baselines.simple_agent:create_agent
```

Baseline runs are written under:

```text
outputs/baseline/<run-name>/
```

The baseline can be configured with:

- `BASELINE_MODEL`
- `BASELINE_MAX_TURNS`
- `BASELINE_MAX_TOKENS`
- `BASELINE_TEMPERATURE`

## Parallel Execution

Use `--n-workers` to run independent problems concurrently:

```bash
.venv/bin/python run.py \
  --problems sample-problems \
  --out outputs \
  --n-workers 2
```

Each worker receives its own process, budget ledger, deadline, output
directory, and Lean container. The value of `--n-workers` does not create
additional model calls within a single problem.

## Checks

Run the no-key smoke test:

```bash
bash scripts/smoke_test.sh
```

Before submitting, run the judging contract check:

```bash
bash scripts/judge_check.sh
```

## Output Artifacts

For each problem, the runner writes:

- `solution.lean`
- `result.json`
- `transcript.json`
- `events.jsonl`
- `checkpoint.json`
- `worker-config.json`

The run directory also contains:

- `run.json`
- `summary.json`

The `events.jsonl` file is append-only and flushed incrementally. The
`transcript.json` file is derived from those events and contains the full LLM
requests, responses, token usage, costs, timings, and errors with secrets
redacted.

To rescore saved solutions, pass the concrete run directory:

```bash
bash scripts/rescore.sh outputs/submission/20260819T120000Z
```

## Scoring

A problem receives one point when all of the following conditions hold:

- Comparator accepts every required declaration.
- Numeric answer declarations, when present, have valid literal bodies.
- Actual OpenRouter spend is at most `$1.00`.
- The problem finishes within its deadline.

Model participation is reported in `result.json`. It is reviewed separately
from the mechanical one-point score.

See `RULES.md` for the complete assignment rules.

## Repository Structure

| Path | Purpose |
| --- | --- |
| `RULES.md` | Assignment rules, budgets, and judging behavior |
| `submission/agent.py` | Applicant implementation |
| `baselines/` | Reference agent implementations |
| `src/re_harness/` | Runner, services, accounting, logs, and evaluator |
| `sample-problems/` | Public problems and versioned manifest |
| `docker/` | Source for the Lean runtime image |
| `docs/` | Agent API, setup, artifacts, and security model |
| `scripts/` | Setup, smoke test, rescore, and judging checks |

## Submission notes (applicant)

The coordination layer is `submission/agent.py` with its text utilities in
`submission/lean_text.py`. It implements the `docs/AGENT_API.md` contract
unchanged: `python run.py --problems <set> --out <out-root>` runs it with the
default configuration, and `scripts/judge_check.sh` passes.

**Design in one paragraph.** A staged, anytime escalation ladder runs inside
the harness's fail-closed budget rails: a deterministic tactic sweep (S0), an
answer-consensus gate for answer-type problems (S0.5), pooled cross-model
sampling selected by the REPL (S1), a baseline-style chronological repair
chain (S1r), capped compiler-guided repair (S2), a plateau handoff to the
other model (S3), sketch-and-fill decomposition with a persistent lemma pool
(S4), and finalization (S5). Every accepted winner is re-checked with the
kit's own Comparator in a fresh container before it is returned (the
precheck), and every candidate is composed on the challenge's exact import
block. The two models never exchange messages; they interact only through
artifacts (candidate files, error histories, skeletons).

**Configuration.** Everything is an environment variable with a tested
default; the judged configuration is the default.

| Variable | Default | Meaning |
| --- | --- | --- |
| `SUBMISSION_MODELS` | `duo` | `duo`, `qwen`, or `gptoss` (the solo arms used in the writeup) |
| `SUBMISSION_QWEN_SAMPLES` / `SUBMISSION_GPTOSS_SAMPLES` | `8` / `2` | S1 wave sizes |
| `SUBMISSION_REPAIR_ROUNDS` / `SUBMISSION_SKETCH_ROUNDS` | `4` / `4` | S2 and S4 round caps |
| `SUBMISSION_GPTOSS_CALL_CAP` | `10` | per-problem cap on GPT-OSS calls |
| `SUBMISSION_SHORTCAP` | `1` | window-proportional time constants (identity at 40-minute or longer windows) |
| `SUBMISSION_FILL_BREADTH` | `1` | breadth-first hole filling in S4 |
| `SUBMISSION_COMPARE_PRECHECK` | `1` | Comparator precheck of accepted winners |
| `SUBMISSION_SURFACE_REPAIR` | `1` | core-tactic repair when a narrow-import challenge rejects a proof at the precheck |
| `SUBMISSION_RAW_LOOP` / `_TURNS` / `_SHARE` | `1` / `16` / `0.45` | the S1r chain, its turn cap, and its share of the window |
| research flags, all default off | `""` | `SUBMISSION_{PLAN_FIRST,WAVE_SPREAD,TYPED_FILLS,PREMISE_HINTS,CLUSTER_REPAIR,CRITIC_NOTES,SUGGEST_HARVEST,STRENGTHEN_IH,SKELETON_KEEP,SKELETON_PORTFOLIO,BOUND_TEMPLATES,FILL_REASONING,DIALOGUE_REPAIR,DIALOGUE_SKETCH}` |

`SUBMISSION_DISABLE_LLM=1` runs the deterministic stages only (no model calls).

**Harness provenance.** `src/re_harness/` is the kit's harness at its current
upstream revision with two small additions, both optional for agents and
inert for the kit baselines: `Services.compare`, a real-Comparator precheck
callable exposed by `worker.py` (it runs the kit's own scoring program on a
candidate and returns pass/timeout plus the diagnostic tail), and
`Services.state_dir`, the problem's output directory, which the agent uses
to persist its search state. No retry, fallback, or accounting behavior of
the harness was changed.

**Other applicant material.**

| Path | Contents |
| --- | --- |
| `tests/test_*.py` (submission, surface repair, raw loop, dialogue, pair agent, ...) | offline unit tests for the coordination layer (`.venv/bin/python -m pytest tests -q`) |
| `baselines/pair_agent.py` | the scaffold-free control arm from the writeup: two kit repair loops in one window, first accepted proof wins (`--agent baselines.pair_agent:create_agent`) |
| `custom-problems-dev/`, `custom-problems-held/`, `custom-problems-all/` | the 24-problem custom benchmark in kit format (16 development, 8 validation) |
| `reference/`, `reference-custom/` | Comparator-verified reference proofs for the kit's hard problems and for every custom problem; documentation only, never read by the agent |
| `scripts/check_lean.py`, `scripts/validate_references.py`, `scripts/assemble_customset.py`, `scripts/analyze_runs.py` | reference-proof checking, benchmark assembly, and run comparison |

The complete experiment record (every run's `result.json`, `solution.lean`
and summaries, the experiment log, and the research-loop notes) is kept on
a separate research branch of this repository;
the writeup is submitted separately as a PDF.

**No per-problem special-casing.** Runtime prompts contain only generic
technique material, and the reference proofs are never inputs.
