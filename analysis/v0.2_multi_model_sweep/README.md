# v0.2 Multi-Model Benchmark Sweep

## What this benchmark measures

The Ethereum Verification Benchmark evaluates how well LLMs can write **formal proofs in Lean 4** about Ethereum smart contract behavior. Each task gives the model a Solidity contract's specification and asks it to produce a machine-checkable Lean proof. A proof is only counted as solved if it passes the Lean verifier — no `sorry`, no axioms, no shortcuts.

This sweep tests multiple frontier models side-by-side to compare their formal verification capabilities.

## Benchmark Configuration

| Parameter | Value |
|---|---|
| Release | v0.2 (immutable) |
| HEAD | `c5a2344b121040445ccd745a3f839548ca8f9158` |
| Lean | 4.24.0 |
| Harness | `sha256:244bbf5ca68050dd4a7e56bdb794a68bc01a74d169828039e0943e511f65f867` |
| Total tasks | 240 |

## Panels

Three nested panels balance coverage vs. cost. FAST-12 ⊂ STRAT-50 ⊂ FULL-240.

| Panel | Tasks | Role |
|---|---|---|
| **FULL-240** | 240 | All benchmark tasks. The most complete picture of model capability. Highest token cost. |
| **STRAT-50** | 50 | Representative stratified sample (seed=42, ~1–2 tasks per task group). Gives an unbiased estimate of FULL-240 performance at ~20% of the cost. |
| **FAST-12** | 12 | Minimal subset (first 12 tasks of STRAT-50). Primarily for quick testing and broad model sweeps where you need results fast. |

## Effort Profiles

| Profile | Max attempts | Max tool calls | Use case |
|---|---|---|---|
| p1_release | 2 | 24 | Release baseline — minimal effort |
| p4_normal | 16 | 120 | Full effort — maximizes solve rate |

## Results

### Models with real Lean verdicts

| # | Model | Panel | Solved | Evaluated | Rate | Profile |
|---|---|---|---|---|---|---|
| 1 | **gpt-5.6-sol** | FAST-12 | 6 | 12 | **50.0%** | p4_normal |
| 2 | **gpt-5.6-terra** | FAST-12 | 4 | 16 | **25.0%** | p4_normal |
| 3 | gpt-5.6-luna | FAST-12 | 3 | 12 | 25.0% | p4_normal |
| 4 | openai/gpt-5.5 | FAST-12 | 2 | 9 | 22.2% | p1_release |
| 5 | anthropic/claude-opus-5 | FAST-12 | 2 | 11 | 18.2% | p1_release |
| 6 | minimax/MiniMax-M2.7 | FAST-12 | 1 | 12 | 8.3% | p1_release |
| 7 | minimax/MiniMax-M3 | FULL-240 | 12 | 228 | 5.3% | p1_release |

**Coverage note**: STRAT-50 was partially tested (gpt-5.6-terra, 16/50 tasks) but never completed by any model. FULL-240 was completed only by MiniMax-M3.

### MiniMax-M3 on all panels (from FULL-240 data, p1_release)

| Panel | Solved | Evaluated | Rate |
|---|---|---|---|
| FULL-240 | 12 | 228 | 5.3% |
| STRAT-50 | 5 | 50 | 10.0% |
| FAST-12 | 0 | 12 | 0.0% |

### Key findings

1. **Effort dominates model choice**: GPT-5.6 at p4_normal (16/120) achieves 25–50%. MiniMax-M3 at p1_release (2/24) stays at 0–5%. The same model with 8× more attempts and 5× more tool calls would likely improve dramatically.
2. **GPT-5.6 family is strongest**: sol (50%) > terra (25%) ≈ luna (25%), all producing valid Lean proofs.
3. **Claude Opus-5 works through the harness** (18.2%) — the first Anthropic model to produce real Lean verdicts in this benchmark.

## Models Not Covered

These models were attempted but could not produce results. The proxy allows an initial request but enters a persistent cooldown after the first API call, blocking the harness which requires multiple round-trips per task.

| Model | Pattern | Infra count |
|---|---|---|
| anthropic/claude-fable-5 | request 1 OK (~1.7k tokens), request 2 → 502→429 cooldown | 12/12 |
| anthropic/claude-sonnet-5 | same pattern | 12/12 |
| openai/gpt-5.6 | same pattern | 12/12 |
| zai/glm-5.2 | same pattern | 12/12 |
| zai/glm-4.7 | same pattern | 12/12 |
| muse/muse-spark-1.1 | same pattern | 12/12 |
| muse/muse-spark-1.2 | same pattern | 12/12 |
| kimi/k3 | rate-limited (quota) | 12/12 |

**Root cause**: Per-provider cooldown in the sandboxed.sh proxy that triggers after 1–2 successive requests for non-MiniMax/non-GPT-5.6 providers. Once triggered, the cooldown persists for 1h+. This is an infrastructure limitation, not a model limitation.

## Files

- `leaderboard.json` — structured leaderboard
- `raw_results.json` — per-task raw results (deduplicated across all campaign phases)
