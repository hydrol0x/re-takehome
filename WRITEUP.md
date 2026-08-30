# Submission writeup

The submission writeup is **`writeup.pdf`** (source: `paper.html`), an
arXiv-style paper:

> **Two Models, One Compiler: Verifier-Centric Coordination of Two Fixed
> Off-the-Shelf LLMs for Competition Mathematics in Lean 4**

Its structure: research questions (RQ1 scaffold vs. raw baselines; RQ2
pairing vs. best solo under the same scaffold; RQ3 what enables hard
instances) → task and evaluation protocol (including the evaluation-regimes
table) → system (architecture diagram) → experimental design (datasets,
development boundary, benchmark Comparator-validation) → results by RQ
(including the per-problem complementarity matrix) → ablations and
robustness (mechanism screening, precheck accounting) → related work →
limitations → conclusion, with a standardized 28-entry bibliography.

Appendices in this repository:

| Document | Contents |
| --- | --- |
| `RESEARCH.md` | Harness analysis, model calibration, literature review, architecture rationale |
| `PART2.md` | Extended Part-Two discussion |
| `EXPERIMENTS.md` | Chronological log of every keyed run, with run identifiers |
| `RESEARCH_LOOP.md` | Variant selection and mechanism screening, per-problem composition |
| `RUNBOOK.md` | Reproduction instructions |
| `scripts/validate_references.py`, `outputs/reference-comparator-validation.json` | Comparator validation of the custom benchmark's reference proofs |

Disclosure: developed with substantial assistance from Claude (Anthropic) —
code, experiments, analysis, and writing — as disclosed in the submission
form and `README.md`.
