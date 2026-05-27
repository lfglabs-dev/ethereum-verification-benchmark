<h1 align="center">Verity Benchmark</h1>

<p align="center">
  <strong>Measuring AI agents at formally verifying smart contracts in Lean 4.</strong>
</p>

<p align="center">
  <a href="https://veritylang.com"><img src="https://img.shields.io/badge/docs-veritylang.com-0a7d7d.svg" alt="Verity documentation"></a>
  <a href="https://github.com/lfglabs-dev/verity-benchmark"><img src="https://img.shields.io/badge/built%20with-Lean%204-blueviolet.svg" alt="Built with Lean 4"></a>
  <a href="https://github.com/lfglabs-dev/verity-benchmark/actions"><img src="https://img.shields.io/github/actions/workflow/status/lfglabs-dev/verity-benchmark/check.yml?label=check" alt="Check"></a>
</p>

<p align="center">
  <a href="https://veritylang.com">Documentation</a>
  &nbsp;·&nbsp;
  <a href="https://github.com/lfglabs-dev/verity">Verity compiler</a>
  &nbsp;·&nbsp;
  <a href="https://lfglabs.dev/research/verity-benchmark">Research note</a>
  &nbsp;·&nbsp;
  <a href="https://lfglabs.dev/papers/verity.pdf">Paper (PDF)</a>
</p>

---

## What is this?

**Verity Benchmark** is an open evaluation suite that measures how well AI agents can produce **formal proofs** of smart contract correctness in [Lean 4](https://lean-lang.org/), on top of the [Verity](https://github.com/lfglabs-dev/verity) formally verified smart contract compiler. Cases are drawn from real-world Ethereum protocols, DeFi systems, token standards, and security challenge contracts.

[Verity](https://veritylang.com) lets you write smart contracts, state what they should do, prove correctness, and compile to EVM bytecode with machine-checked proofs that compilation preserves semantics. This benchmark is an initiative made in partnership with the **Ethereum Foundation** and various protocols of the ecosystem. Full documentation lives at [**veritylang.com**](https://veritylang.com); the team behind it is [**LFG Labs**](https://lfglabs.dev).

Each benchmark task gives an agent:
- A fixed contract implementation
- A fixed formal specification
- One editable proof file with a single theorem to prove

The agent must produce a valid Lean proof. No placeholders (`sorry`, `admit`) are allowed, and benchmark proof files may not introduce `axiom` declarations. A small CI-enforced trusted boundary axiom ledger documents semantic boundaries such as fixed-point `exp`/`ln` models.

---

## Benchmark suite

19 active cases, 117 active task manifests, and 8 backlog task manifests are drawn from real-world contracts. All active and backlog task manifests are currently runnable proof tasks with hidden reference proofs.

| Case | Source | Tasks |
|------|--------|-------|
| `alchemix/earmark_conservation` | Alchemix V3 | 5 |
| `balancer/reclamm_swap_rounding` | Balancer ReClamm | 1 |
| `cork/pool_solvency` | Cork Phoenix | 1 |
| `damn_vulnerable_defi/side_entrance` | Damn Vulnerable DeFi | 5 |
| `ethereum/deposit_contract_minimal` | Ethereum deposit contract | 5 |
| `forgeyields/global_solvency` | ForgeYields TokenGateway | 7 |
| `kleros/sortition_trees` | Kleros sortition module | 6 |
| `lagoon/guardrails` | Lagoon vault guardrails | 3 |
| `lido/vaulthub_locked` | Lido VaultHub | 5 |
| `nexus_mutual/ramm_price_band` | Nexus Mutual RAMM | 4 |
| `onedelta/caller_address_integrity` | OneDelta callback caller integrity | 10 |
| `paladin_votes/stream_recovery_claim_usdc` | Paladin Votes | 26 |
| `polygon/agglayer_bridge` | Polygon Agglayer bridge | 2 |
| `reserve/auction_price_band` | Reserve DTF | 4 |
| `safe/owner_manager_reach` | Safe OwnerManager | 15 |
| `termmax/order_v2_buy_xt_single_segment` | TermMax Order V2 | 1 |
| `usual/dao_collateral` | Usual DaoCollateral | 5 |
| `wildcat/borrow_liquidity_safety` | Wildcat V2 | 1 |
| `zama/erc7984_confidential_token` | Zama / OpenZeppelin ERC-7984 | 11 |

Every runnable task includes a reference proof hidden from the agent during benchmarking. Case-level `proof_status: partial` means the broader case family is not fully complete; it does not imply that runnable per-task reference proofs are missing.

Coverage is strongest today for accounting, local state preservation, storage effects, linked-list ownership structures, and solvency invariants. Known thinner areas include reentrancy beyond modeled guards, oracle manipulation, governance/timelock properties, temporal or liveness properties, cross-contract compositional reasoning, cryptographic assumptions, and adversarial EVM-level behavior. See [docs/evaluated-surface.md](./docs/evaluated-surface.md) for the current evaluation surface.

---

## Running the benchmark

### Verify reference proofs

```bash
# Single task
./scripts/run_task.sh ethereum/deposit_contract_minimal/deposit_count

# All tasks in a case
./scripts/run_case.sh ethereum/deposit_contract_minimal

# Full suite
./scripts/run_all.sh
```

### Run with a harness

The supported benchmark harnesses are:

- `default`: built-in Lean-tools harness using local proof candidates plus an OpenAI-compatible API fallback.
- `grok-build`: Grok Build shell harness.

```bash
# Run a single task with the default harness
python3 -m harness.cli run-task lido/vaulthub_locked/locked_funds_solvency --harness default

# Run a full case with the default harness
./scripts/run_default_harness_group.sh lido/vaulthub_locked --max-attempts 2

# Run the full suite with the default harness
./scripts/run_default_harness_suite.sh --suite active --max-attempts 1

# Run Grok Build
VERITY_ALLOW_HOST_GROK_AUTH=1 ./scripts/run_grok_build_group.sh ethereum/deposit_contract_minimal --max-turns 20
./scripts/run_grok_build_suite.sh --suite active

# Compare two run artifacts
python3 -m harness.cli compare --runs results/runs/<default-run> results/runs/<grok-build-run>
```

Default harness API configuration:

```bash
cp .env.example .env
$EDITOR .env
```

Grok Build can use `GROK_CODE_XAI_API_KEY` in CI. For local comparisons against
an already logged-in `grok` CLI, set `VERITY_ALLOW_HOST_GROK_AUTH=1`; the runner
copies only `~/.grok/auth.json` into an isolated temporary home for that run.

---

## Project structure

```
verity-benchmark/
├── Benchmark/
│   ├── Cases/           # Reference proofs (hidden from agents)
│   └── Generated/       # Public proof templates
├── cases/               # Task manifests and contract sources
├── harness/             # Agent runner, tools, and evaluation
├── scripts/             # CLI entry points
├── schemas/             # JSON schemas for results
└── results/             # Run artifacts
```

---

## Documentation

| Document | Description |
|----------|-------------|
| [harness/README.md](./harness/README.md) | Harness internals and agent integration |
| [docs/architecture/task-api.md](./docs/architecture/task-api.md) | Task contract and manifest format |
