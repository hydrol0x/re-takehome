# Handoff — state of play and how to continue

*Standalone context for any fresh session (human or agent) picking up this
work. Everything referenced lives on branch
`claude/coordination-layer-research-h0skps`.*

## The task (30 seconds)

Verified Mechanisms take-home: make two fixed models —
`qwen/qwen3.5-flash-02-23` and `openai/gpt-oss-120b`, via OpenRouter only —
collaborate to solve competition-math problems and prove them in Lean 4
(Mathlib), scored by the official Comparator under caps of **$1 and 8 h per
problem**. Part 2: determine whether the collaboration beats either model
alone, and why. Full rules: `RULES.md`. Judge command:
`OPENROUTER_API_KEY=<key> VM_TIME_LIMIT_S=28800 VM_BUDGET_USD=1.00 python run.py --problems <holdout> --out <out>`.

## Where everything is

| file | what it holds |
| --- | --- |
| `RESEARCH.md` | the full design brief: harness constraints + landmines (§1), baseline empirics (§2), model research (§3), literature evidence (§4), chosen architecture (§6), Part-2 plan (§7), **experiment log (§10)** |
| `RUNBOOK.md` | exact keyed-run sequence: calibration → dev runs → Part-2 arms → final validation, with budget rails |
| `submission/agent.py` | the coordination agent (v2): S0 tactic sweep → S0.5 answer consensus → S1 pooled sampling → S2 repair → S3 plateau handoff → S4 sketch/fill, plus safety rails; arm switch `SUBMISSION_MODELS=duo\|qwen\|gptoss` |
| `submission/lean_text.py` | parsing/splicing/guards (statement safety, banned tokens, literal normalization, axiom audit) |
| `scripts/calibrate.py` | ~$0.10 probe of qwen thinking-mode mapping + gpt-oss effort levels |
| `reference/` | frontier reference proofs + the two broken-problem certificates (see below) |
| `tests/test_submission_text.py` | offline unit tests (`pytest tests/`) |
| `.claude/hooks/session-start.sh` | web-session bootstrap: venv, dockerd, Lean image (idempotent) |

## Established facts (do not re-derive)

1. **Sample-set ceiling is 14/16.** `rmo_2000_6` is mathematically false as
   formalized (compiling disproof in `reference/rmo_2000_6_falsity.lean`);
   `rmo_2000_3`'s challenge file itself fails to build under the Comparator
   (missing `Ico` import — REPL masks it). Do not spend on them.
2. **S0 (free tactic sweep) alone: 6/16 at $0.00** — p01–p05, p08.
3. Baselines (committed, `outputs/baseline/`): qwen 7/16, gpt-oss 8/16,
   union 10/16, complementary failure styles (gpt-oss stuck-loops, qwen
   thrashes). Qwen ran thinking-OFF; gpt-oss at medium effort — both
   upgradable.
4. Reference proofs exist for every provable "hard" problem (p09, p10,
   rmo_2000_2, rmo_2001_2 comparator-verified; rmo_2000_3 REPL-verified).
   If the agent solves those four, the pipeline genuinely works.
5. Harness landmines (details `RESEARCH.md` §1.3–1.4): one HTTP failure
   permanently closes a problem's budget ledger; a deadline kill mid-call
   voids the problem. The agent already defends both — keep it that way.
6. The Putnam-style solution abbrevs accept tautological answers
   (policy discussion: `RESEARCH.md` §6.6).

## What is done vs. not done

Done: research + design; agent v2 implemented with all stages; offline
verification (37 tests green, mock-LLM end-to-end, `judge_check.sh` green on
the free path, `#print axioms` gate live-verified); frontier reference; docs.

**Not done — the live work:**
1. `scripts/calibrate.py` with the real key (validates qwen
   `reasoning:{enabled:true}` mapping and gpt-oss effort levels; fix
   `submission/agent.py` settings if a mapping is broken).
2. Duo dev run: `VM_TIME_LIMIT_S=1800 .venv/bin/python run.py --problems
   sample-problems --out outputs --n-workers 2`, then
   `bash scripts/rescore.sh outputs/submission/<ts>`.
3. Part-2 arms at matched caps: same command with `SUBMISSION_MODELS=qwen`,
   then `gptoss`; compare solves/origins/spend (per-problem origin is in
   `result.json` → `agent_metadata.origin`).
4. Iterate on the observed failure modes; longer-cap runs for the hard tier;
   final `judge_check.sh` + full-cap validation before submission.
5. Part-2 writeup from the arm results + `RESEARCH.md` §7 plan.

## Rails for any run

- Never print, commit, or echo `OPENROUTER_API_KEY` (env var; takes
  precedence over `.env`). `.env` is gitignored; keep it that way.
- Work/push only on `claude/coordination-layer-research-h0skps`;
  `git pull --rebase` before pushing.
- Web container: max `--n-workers 2` (5 GB per Lean container, ~15 GB total).
- Budget: stop and record findings if a single run exceeds ~$5 or cumulative
  experiments exceed ~$15 of the $50 dev key.
- Commit run results per step: `summary.json`, `run.json`, per-problem
  `result.json` + `solution.lean`, plus an `EXPERIMENTS.md` entry
  (skip bulky `events.jsonl`/`transcript.json`).

## Kickoff prompt for a fresh session

> Check out branch `claude/coordination-layer-research-h0skps` and read
> `HANDOFF.md` — then do exactly what its "Not done" list says, in order,
> following its rails. Bootstrap the environment with
> `CLAUDE_CODE_REMOTE=true bash .claude/hooks/session-start.sh` and verify
> with `bash scripts/smoke_test.sh` before spending anything.
