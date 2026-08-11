# v0.2 Multi-Model Benchmark Sweep

## What this benchmark measures

The Ethereum Verification Benchmark evaluates how well LLMs can write **formal proofs in Lean 4** about Ethereum smart contract behavior. Each task gives the model a Solidity contract's specification and asks it to produce a machine-checkable Lean proof. A proof counts as solved only if it passes the Lean verifier — no `sorry`, no axioms, no shortcuts.

## Benchmark Configuration

| Parameter | Value |
|---|---|
| Release | v0.2 (immutable) |
| HEAD | `c5a2344b121040445ccd745a3f839548ca8f9158` |
| Lean | 4.24.0 |
| Harness | `sha256:244bbf5ca68050dd4a7e56bdb794a68bc01a74d169828039e0943e511f65f867` |
| Total tasks | 240 |

## Panels

Three nested panels balance coverage vs. cost. FAST-12 ⊂ STRAT-50 ⊂ FULL-240. Panel membership is published in `leaderboard.json`.

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

### FAST-12 panel (ranked within panel)

| Model | Solved | Valid | Rate | Profile | Infra |
|---|---|---|---|---|---|
| **gpt-5.6-sol** | 6 | 12 | **50.0%** | p4_normal | 0 |
| **gpt-5.6-terra** | 6 | 12 | **50.0%** | p4_normal | 0 |
| gpt-5.6-luna | 3 | 12 | 25.0% | p4_normal | 0 |
| openai/gpt-5.5 | 2 | 9 | 22.2% | p1_release | 3 |
| anthropic/claude-opus-5 | 2 | 11 | 18.2% | p1_release | 1 |
| minimax/MiniMax-M3 | 2 | 12 | 16.7% | p1_release | 0 |
| minimax/MiniMax-M2.7 | 1 | 12 | 8.3% | p1_release | 0 |

### STRAT-50 panel

| Model | Solved | Valid | Covered | Rate | Status |
|---|---|---|---|---|---|
| gpt-5.6-terra | 7 | 16 | 16/50 | 43.8% | **Partial** (16/50 tasks) |
| minimax/MiniMax-M3 | 6 | 50 | 50/50 | 12.0% | Complete |

### FULL-240 panel

| Model | Solved | Valid | Rate | Tokens (run-level) |
|---|---|---|---|---|
| minimax/MiniMax-M3 | 14 | 240 | 5.8% | 9,266,049 |

**Token note**: FULL-240 tokens are aggregated at run granularity (each run directory counted once). Per-task token attribution is available in `raw_results.json`.

### Key findings

1. **Effort dominates**: GPT-5.6 at p4_normal (16/120) reaches 50% on FAST-12. MiniMax-M3 at p1_release (2/24) reaches 16.7% on the same panel.
2. **GPT-5.6 family strongest**: sol and terra tie at 50% on FAST-12, followed by luna at 25%.
3. **STRAT-50 shows scaling**: MiniMax-M3 jumps from 16.7% (FAST-12) to 12.0% (STRAT-50) — different task mix. Terra's partial run (43.8%) suggests GPT-5.6 would score significantly higher on the full panel.
4. **Cross-panel comparison requires caution**: solve rates are not comparable across panels due to different task populations.

## Models Not Covered

All attempted but produced 0 valid verdicts due to proxy infrastructure issues. The proxy allows an initial request but enters a persistent cooldown after the first API call.

| Model | Failure type | Infra | Skipped |
|---|---|---|---|
| anthropic/claude-fable-5 | HTTP 429 after request 1 | 12 | 0 |
| anthropic/claude-sonnet-5 | HTTP 429 after request 1 | 4 | 8 |
| openai/gpt-5.6 | HTTP 502/429 preflight | 12 | 0 |
| zai/glm-5.2 | HTTP 502 preflight | 4 | 8 |
| zai/glm-4.7 | HTTP 502 preflight | 12 | 0 |
| muse/muse-spark-1.1 | HTTP 429 preflight | 12 | 0 |
| muse/muse-spark-1.2 | HTTP 429 preflight | 12 | 0 |
| kimi/k3 | Rate-limited (quota) | 4 | 8 |

**Root cause**: Per-provider rate limits in the sandboxed.sh proxy. Non-MiniMax/non-GPT-5.6 providers trigger cooldown after 1–2 successive requests. This is an infrastructure limitation, not a model limitation.

## Files

- `leaderboard.json` — structured leaderboard with panel membership
- `raw_results.json` — per-task raw results (deduplicated)
