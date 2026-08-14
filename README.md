<h1 align="center">Ethereum Verification Benchmark</h1>

<p align="center">
  <strong>AI agents proving Ethereum smart contract properties in Lean 4.</strong>
</p>

<p align="center">
  <a href="https://lfglabs.dev/benchmark"><img src="https://img.shields.io/badge/leaderboard-lfglabs.dev%2Fbenchmark-0a7d7d.svg" alt="Public leaderboard"></a>
  <a href="https://veritylang.com"><img src="https://img.shields.io/badge/docs-veritylang.com-0a7d7d.svg" alt="Verity documentation"></a>
  <a href="https://github.com/lfglabs-dev/ethereum-verification-benchmark/actions"><img src="https://img.shields.io/github/actions/workflow/status/lfglabs-dev/ethereum-verification-benchmark/check.yml?label=check" alt="Check"></a>
</p>

<p align="center">
  <a href="https://lfglabs.dev/benchmark">Leaderboard</a>
  &nbsp;·&nbsp;
  <a href="./leaderboard.md">Committed results</a>
  &nbsp;·&nbsp;
  <a href="./docs/running-benchmark.md">Run guide</a>
  &nbsp;·&nbsp;
  <a href="./docs/evaluated-surface.md">Evaluation surface</a>
  &nbsp;·&nbsp;
  <a href="https://veritylang.com">Verity docs</a>
</p>

---

## What This Is

Ethereum Verification Benchmark is an open benchmark for measuring whether AI agents can produce machine-checked proofs of smart contract correctness.

Each task gives an agent:

- a fixed contract implementation,
- a fixed formal specification,
- one editable Lean proof file,
- one target theorem.

The agent passes only if Lean accepts the proof. The verifier rejects theorem changes, hidden imports, `sorry`, `admit`, `axiom`, and other benchmark-policy violations.

The suite uses [Verity](https://github.com/lfglabs-dev/verity), a Lean 4 EDSL for modeling EVM smart contracts with a shallow embedding. Verity also provides a proven compilation pipeline backed by a deep embedding, but this benchmark does not exercise that pipeline.

The benchmark is maintained by [LFG Labs](https://lfglabs.dev) in partnership with the Ethereum Foundation and ecosystem protocols.

## Results

The public dashboard is [lfglabs.dev/benchmark](https://lfglabs.dev/benchmark).

Committed result data lives in:

- [leaderboard.md](./leaderboard.md)
- [results/index.json](./results/index.json)
- [results/leaderboards/](./results/leaderboards/)
- [results/manifests/](./results/manifests/)
- [results/summaries/](./results/summaries/)

Version `0.3` is the current benchmark environment: 263 frozen tasks on Lean 4.31. New comparable model campaigns should use the reproducible [v0.3 STRAT-50 panel](./analysis/v0.3_strat50/README.md). Version `0.1` remains the older public-dashboard baseline, while v0.2/Lean 4.24 artifacts remain frozen for historical reproduction only. Results from different benchmark versions or inference protocols are separate cohorts and must not be combined.

## Quick Start

Verify one reference proof:

```bash
./scripts/run_task.sh ethereum/deposit_contract_minimal/deposit_count
```

Run one task through the fair default harness:

```bash
cp .env.example .env
$EDITOR .env
python3 -m harness.cli run-task ethereum/deposit_contract_minimal/deposit_count --harness default
```

Run the local checks used by CI:

```bash
python3 scripts/check.py
```

## Repository Layout

| Path | Purpose |
|------|---------|
| `cases/` | Active benchmark cases and task manifests |
| `backlog/` | Runnable tasks not yet in the active suite |
| `Benchmark/` | Lean modules for contracts, specs, proofs, and shared Grindset lemmas |
| `harness/` | Canonical fair harness, metering, and verifier policy |
| `scripts/` | Verification, aggregation, release, and analysis tooling |
| `benchmark-versions/` | Version manifests and compatibility fingerprints |
| `results/` | Published result indexes, summaries, and leaderboards |
| `docs/` | Architecture, operation, and evaluation notes |

## Docs

- [Run and publish benchmark results](./docs/running-benchmark.md)
- [v0.3 STRAT-50 panel and campaign guide](./analysis/v0.3_strat50/README.md)
- [Harness internals](./harness/README.md)
- [Task API](./docs/architecture/task-api.md)
- [Results publication model](./docs/architecture/results-publication.md)
- [Evaluation surface](./docs/evaluated-surface.md)
