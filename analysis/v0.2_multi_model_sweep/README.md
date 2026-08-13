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
| **FULL-240** | 240 | All benchmark tasks. The most complete picture of model capability. |
| **STRAT-50** | 50 | Representative stratified sample (seed=42, ~1–2 tasks per task group). Unbiased estimate at ~20% of FULL-240 cost. |
| **FAST-12** | 12 | Minimal subset for quick testing and broad model sweeps. |

## Effort Profiles

| Profile | Max attempts | Max tool calls | Use case |
|---|---|---|---|
| p1_release | 2 | 24 | Release baseline — minimal effort |
| p4_normal | 16 | 120 | Full effort — maximizes solve rate |

## Results

### STRAT-50 (p4_normal, 50/50 tasks per model)

| Model | Solved | Valid | Rate | Tokens |
|---|---|---|---|---|
| **gpt-5.6-sol** | 17 | 50 | **34,0%** | 1,46M |
| **gpt-5.6-terra** | 10 | 50 | **20,0%** | 1,36M |
| gpt-5.6-luna | 9 | 50 | 18,0% | 1,01M |
| minimax/MiniMax-M3 | 7 | 50 | 14,0% | 2,24M |

### FAST-12 (p4_normal for GPT-5.6, p1_release for others)

| Model | Solved | Valid | Rate | Profile |
|---|---|---|---|---|
| **gpt-5.6-sol** | 6 | 12 | **50,0%** | p4_normal |
| **gpt-5.6-terra** | 6 | 12 | **50,0%** | p4_normal |
| gpt-5.6-luna | 3 | 12 | 25,0% | p4_normal |
| openai/gpt-5.5 | 2 | 9 | 22,2% | p1_release |
| anthropic/claude-opus-5 | 2 | 11 | 18,2% | p1_release |
| minimax/MiniMax-M3 | 2 | 12 | 16,7% | p1_release |
| minimax/MiniMax-M2.7 | 1 | 12 | 8,3% | p1_release |

### FULL-240 (p1_release)

| Model | Solved | Valid | Rate | Tokens (run-level) |
|---|---|---|---|---|
| minimax/MiniMax-M3 | 14 | 240 | 5,8% | 9,266,049 |

## Cross-Panel Findings

### Same-panel effort comparison (MiniMax-M3)

| Effort | Panel | Rate |
|---|---|---|
| p1_release (2/24) | STRAT-50 | 12,0% |
| p4_normal (16/120) | STRAT-50 | **14,0%** |

On the same STRAT-50 tasks, increasing the budget from p1 to p4 improves the observed solve rate by 2 percentage points (6/50 to 7/50). The separate FULL-240 p1 result is 14/240 (5,8%), but it is not an effort-controlled comparison because the panel also changes.

### Cross-model comparison (STRAT-50 at p4_normal)

GPT-5.6 dominates: sol (34%) > terra (20%) ≈ luna (18%). MiniMax-M3 trails at 14% despite higher token spend — the GPT-5.6 family is significantly more efficient at producing valid Lean proofs.

### Key findings

1. **GPT-5.6 strongest**: All three GPT-5.6 variants produce valid Lean proofs on STRAT-50, with sol leading at 34%.
2. **Effort has a modest same-panel effect for MiniMax-M3**: on STRAT-50, p4 solves 7/50 versus 6/50 at p1 (14,0% versus 12,0%).
3. **Cross-panel comparison requires caution**: STRAT-50 has different task distribution than FAST-12 — sol drops from 50% to 34%.

## Models Not Covered (infrastructure limitation)

| Model | Failure | Infra | Skipped |
|---|---|---|---|
| anthropic/claude-fable-5 | 502/429 (preflight) | 20 | 34 |
| anthropic/claude-sonnet-5 | 502/429 (preflight) | 25 | 34 |
| zai/glm-5.2 | 502 (provider auth) | 20 | 34 |
| zai/glm-4.7 | 502/429 (not run on STRAT-50) | — | — |
| muse/muse-spark-1.1/1.2 | 429 (proxy cooldown) | 20 | 34 |
| openai/gpt-5.6 | 502/429 (preflight) | — | — |
| kimi/k3 | Cooldown (quota) | 25 | 34 |

The proxy's preflight requests fail consistently for these providers, even though simple curl requests succeed. The circuit breaker attempted 3 recovery cycles (10 min cooldown each) before permanently closing.

## Files

- `leaderboard.json` — structured leaderboard with panel membership
- `raw_results.json` — FAST-12 + FULL-240 raw results
- `strat50/results.json` — STRAT-50 raw results (367 rows)
- `strat50/summary.json` — per-model summary
