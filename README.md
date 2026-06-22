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

The suite runs on [Verity](https://github.com/lfglabs-dev/verity), a formally verified smart contract compiler. The benchmark is maintained by [LFG Labs](https://lfglabs.dev) in partnership with the Ethereum Foundation and ecosystem protocols.

## Results

The public dashboard is [lfglabs.dev/benchmark](https://lfglabs.dev/benchmark).

Committed result data lives in:

- [leaderboard.md](./leaderboard.md)
- [results/index.json](./results/index.json)
- [results/leaderboards/](./results/leaderboards/)
- [results/manifests/](./results/manifests/)
- [results/summaries/](./results/summaries/)

Version `0.1` is the current published baseline: 135 active tasks drawn from production protocols, standards, bridges, auctions, vaults, and security challenge contracts. Complete model rows are rankable; partial rows are retained for transparency.

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
| `harness/` | Fair harness, agent adapters, metering, and verifier policy |
| `scripts/` | Verification, aggregation, release, and analysis tooling |
| `benchmark-versions/` | Version manifests and compatibility fingerprints |
| `results/` | Published result indexes, summaries, and leaderboards |
| `docs/` | Architecture, operation, and evaluation notes |

## Docs

- [Run and publish benchmark results](./docs/running-benchmark.md)
- [Harness internals](./harness/README.md)
- [Task API](./docs/architecture/task-api.md)
- [Results publication model](./docs/architecture/results-publication.md)
- [Evaluation surface](./docs/evaluated-surface.md)

