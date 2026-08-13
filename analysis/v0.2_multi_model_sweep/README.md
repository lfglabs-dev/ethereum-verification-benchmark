# v0.2 STRAT-50 Multi-Model Benchmark

## What this benchmark measures

The Ethereum Verification Benchmark evaluates whether LLMs can produce machine-checkable Lean 4 proofs about Ethereum smart-contract behavior. A task is solved only when the generated proof passes the Lean verifier without `sorry`, unauthorized axioms, or shortcuts.

## Frozen configuration

| Parameter | Value |
|---|---|
| Release | v0.2 (immutable) |
| Benchmark HEAD | `c5a2344b121040445ccd745a3f839548ca8f9158` |
| Lean | 4.24.0 |
| Harness | `sha256:244bbf5ca68050dd4a7e56bdb794a68bc01a74d169828039e0943e511f65f867` |
| Panel | STRAT-50, 50 tasks, seed 42 |
| Effort | `p4_normal`: 16 attempts, 120 tool calls |

STRAT-50 is a stratified evaluation panel selected from the 240-task v0.2 release. This publication reports the direct observed rate on those 50 tasks; it does not claim an unweighted estimate of FULL-240 performance.

## Results — STRAT-50 at uniform effort

All four scored models completed the same 50 tasks with the same `p4_normal` budget. Infrastructure-invalid outcomes are not included as model failures; these four cohorts contain 50 genuine verifier verdicts each and zero infrastructure-invalid outcomes.

| Rank | Model | Solved | Valid verdicts | Rate | Tokens |
|---:|---|---:|---:|---:|---:|
| 1 | **gpt-5.6-sol** | **17** | 50 | **34.0%** | 1,461,614 |
| 2 | **gpt-5.6-terra** | **10** | 50 | **20.0%** | 1,362,190 |
| 3 | **gpt-5.6-luna** | **9** | 50 | **18.0%** | 1,013,748 |
| 4 | **minimax/MiniMax-M3** | **7** | 50 | **14.0%** | 2,242,130 |

GPT-5.6 Sol leads this uniform-effort panel. MiniMax-M3 used the most tokens and obtained the lowest solve rate among the four complete cohorts.

## Providers without a score

`zai/glm-5.2`, `muse/muse-spark-1.2`, and `kimi/k3` did not produce a complete verifier-backed STRAT-50 cohort. They are deliberately excluded from the public leaderboard and its denominator and must be rerun after the inference path is repaired; absence of a score is not a zero score.

## Published evidence

- `leaderboard.json` — machine-readable STRAT-50 leaderboard, panel membership, effort, and totals.
- `strat50/results.json` — exactly 200 task outcomes: four models × 50 tasks.
- `strat50/summary.json` — per-model aggregates regenerated from those 200 rows.
- `strat50/run-artifact-index.json` — task-to-run archive index with per-file SHA-256 checksums.
- `strat50/run-archive.tar.gz` — submitted proofs, verifier outputs, conversations, and run metadata for all 200 evaluated tasks.

The `run_dir` fields in `strat50/results.json` are relative paths inside the published archive, not host-local paths.
