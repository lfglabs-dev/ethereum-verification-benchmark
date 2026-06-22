<h1 align="center">Verity Benchmark</h1>

<p align="center">
  <strong>Measuring AI agents at formally verifying smart contracts in Lean 4.</strong>
</p>

<p align="center">
  <a href="https://lfglabs.dev/benchmark"><img src="https://img.shields.io/badge/benchmark-lfglabs.dev%2Fbenchmark-0a7d7d.svg" alt="Public benchmark"></a>
  <a href="https://veritylang.com"><img src="https://img.shields.io/badge/docs-veritylang.com-0a7d7d.svg" alt="Verity documentation"></a>
  <a href="https://github.com/lfglabs-dev/verity-benchmark"><img src="https://img.shields.io/badge/built%20with-Lean%204-blueviolet.svg" alt="Built with Lean 4"></a>
  <a href="https://github.com/lfglabs-dev/verity-benchmark/actions"><img src="https://img.shields.io/github/actions/workflow/status/lfglabs-dev/verity-benchmark/check.yml?label=check" alt="Check"></a>
</p>

<p align="center">
  <a href="https://lfglabs.dev/benchmark">Public leaderboard</a>
  &nbsp;·&nbsp;
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

**Verity Benchmark** is an open evaluation suite for measuring whether AI agents can produce **formal proofs** of smart contract correctness in [Lean 4](https://lean-lang.org/). Cases are drawn from production Ethereum protocols, DeFi systems, token standards, and security challenge contracts, and run on top of the [Verity](https://github.com/lfglabs-dev/verity) formally verified smart contract compiler.

[Verity](https://veritylang.com) lets you write smart contracts, state what they should do, prove correctness, and compile to EVM bytecode with machine-checked proofs that compilation preserves semantics. This benchmark is an initiative made in partnership with the **Ethereum Foundation** and various protocols of the ecosystem. Full documentation lives at [**veritylang.com**](https://veritylang.com); the team behind it is [**LFG Labs**](https://lfglabs.dev).

Each benchmark task gives an agent:
- A fixed contract implementation
- A fixed formal specification
- One editable proof file with a single theorem to prove

The agent must produce a valid Lean proof. No placeholders (`sorry`, `admit`) are allowed, and benchmark proof files may not introduce `axiom` declarations. A small CI-enforced trusted boundary axiom ledger documents semantic boundaries such as fixed-point `exp`/`ln` models.

---

## Benchmark suite

25 active cases, 135 active task manifests, and 8 backlog task manifests are drawn from real-world contracts. All active and backlog task manifests are currently runnable proof tasks with hidden reference proofs.

| Case | Source | Tasks |
|------|--------|-------|
| `alchemix/earmark_conservation` | Alchemix V3 | 5 |
| `balancer/reclamm_swap_rounding` | Balancer ReClamm | 1 |
| `cork/pool_solvency` | Cork Phoenix | 1 |
| `damn_vulnerable_defi/side_entrance` | Damn Vulnerable DeFi | 5 |
| `ethereum/deposit_contract_minimal` | Ethereum deposit contract | 5 |
| `forgeyields/global_solvency` | ForgeYields TokenGateway | 7 |
| `ipor/plasma_vault_redeem_split` | IPOR Plasma Vault | 2 |
| `kleros/sortition_trees` | Kleros sortition module | 6 |
| `lagoon/guardrails` | Lagoon vault guardrails | 3 |
| `lido/vaulthub_locked` | Lido VaultHub | 5 |
| `nexus_mutual/ramm_price_band` | Nexus Mutual RAMM | 4 |
| `onedelta/caller_address_integrity` | OneDelta callback caller integrity | 10 |
| `paladin_votes/stream_recovery_claim_usdc` | Paladin Votes | 26 |
| `piku/fund_conservation` | Piku / Inverter oracle funding manager | 4 |
| `polaris/bonding_curve` | Polaris bonding curve | 4 |
| `polygon/agglayer_bridge` | Polygon Agglayer bridge | 2 |
| `reserve/auction_price_band` | Reserve DTF | 4 |
| `rootstock/flyover_quote_lifecycle` | Rootstock Flyover quote lifecycle | 3 |
| `safe/owner_manager_reach` | Safe OwnerManager | 15 |
| `term_finance/term_auction_clearing` | Term Finance auction clearing | 1 |
| `termmax/order_v2_buy_xt_single_segment` | TermMax Order V2 | 1 |
| `usual/dao_collateral` | Usual DaoCollateral | 5 |
| `wildcat/borrow_liquidity_safety` | Wildcat V2 | 1 |
| `zodiac/roles_decoder_faithfulness` | Zodiac Roles decoder | 3 |
| `zama/erc7984_confidential_token` | Zama / OpenZeppelin ERC-7984 | 12 |

Every runnable task includes a reference proof hidden from the agent during benchmarking. Case-level `proof_status: partial` means the broader case family is not fully complete; it does not imply that runnable per-task reference proofs are missing.

Coverage is strongest today for accounting, local state preservation, storage effects, linked-list ownership structures, and solvency invariants. Known thinner areas include reentrancy beyond modeled guards, oracle manipulation, governance/timelock properties, temporal or liveness properties, cross-contract compositional reasoning, cryptographic assumptions, and adversarial EVM-level behavior. See [docs/evaluated-surface.md](./docs/evaluated-surface.md) for the current evaluation surface.

---

## Results

[![Verity bench](https://img.shields.io/endpoint?url=https%3A%2F%2Fraw.githubusercontent.com%2Flfglabs-dev%2Fverity-benchmark%2Fmain%2Fbadges%2Foverall.json)](./leaderboard.md)
[![GLM 5.2](https://img.shields.io/endpoint?url=https%3A%2F%2Fraw.githubusercontent.com%2Flfglabs-dev%2Fverity-benchmark%2Fmain%2Fbadges%2Fzai-glm-5-2.json)](./leaderboard.md)
[![MiniMax M3](https://img.shields.io/endpoint?url=https%3A%2F%2Fraw.githubusercontent.com%2Flfglabs-dev%2Fverity-benchmark%2Fmain%2Fbadges%2Fminimax-minimax-m3.json)](./leaderboard.md)
[![Kimi K2.7](https://img.shields.io/endpoint?url=https%3A%2F%2Fraw.githubusercontent.com%2Flfglabs-dev%2Fverity-benchmark%2Fmain%2Fbadges%2Fkimi-kimi-for-coding.json)](./leaderboard.md)

The public leaderboard is at [lfglabs.dev/benchmark](https://lfglabs.dev/benchmark). It shows the current benchmark version, model pass rates, solved/failed counts, and run cost estimates.

Current committed results are for benchmark version `0.1`, the 135-task active suite. See [leaderboard.md](./leaderboard.md) for rankable complete rows and transparent partial rows. Detailed per-task traces are archived as GitHub release assets, with committed indexes in `results/manifests/` and aggregate summaries in `results/summaries/`.

Each agent runs in an isolated workspace with reference proofs withheld. A verifier recompiles the submitted file and rejects theorem-statement changes, hidden imports, placeholders, and added assumptions. Token usage is metered at the API boundary when the provider reports it.

## Running the benchmark

### Benchmark versions and incremental reruns

Benchmark results are tied to explicit version manifests in `benchmark-versions/`.
Version `0.1` is the committed baseline and contains the ordered 135-task active
suite plus these compatibility fingerprints:

- `task_set_id`: ordered task refs for the version.
- `task_fingerprint`: execution-relevant task files and manifest fields.
- `task_interface_id`: public/editable files and fields visible to models.
- `harness_id`: harness code, policies, prompts, runner scripts, and agent configs.
- `environment_id`: Lean/Lake toolchain and runtime dependency pins.

Create or refresh a version manifest:

```bash
python3 scripts/compute_fingerprints.py \
  --version 0.2 \
  --created-at 2026-06-16 \
  --out benchmark-versions/v0.2.json
```

Plan incremental reruns for a model:

```bash
python3 scripts/plan_rerun.py \
  --from benchmark-versions/v0.1.json \
  --to benchmark-versions/v0.2.json \
  --model minimax/minimax-m3 \
  --results-manifest results/manifests/v0.1.json \
  --json-out results/rerun-plans/minimax-v0.1-to-v0.2.json
```

The planner reruns all tasks when `harness_id`, `mode`, or `budget` changes,
reruns all tasks on an `environment_id` change unless `--allow-env-compatible`
is passed, reruns added tasks and changed task/interface fingerprints, excludes
removed tasks, and rejects reuse of zero-token, missing-verifier, or error-only
artifacts. Before reusing an indexed result it also re-validates the stored row
against the target task: the row's own `task_fingerprint`/`task_interface_id`
must match the target version, and its stored `result_key` must reproduce from
that recorded context plus the manifest's current `temperature_policy`/`caveats`
(which feed the key), so stale/duplicate rows or post-hoc temperature/caveat
edits force a rerun instead of a silent mismatched reuse.

Use the JSON plan's `rerun[].task_ref` values as the changed-task run list, then
publish detailed run directories as release archives rather than committing
large per-task artifacts. The committed `results/manifests/v<version>.json`
indexes those archives by release tag, asset name, byte size, SHA-256, caveats,
and per-task result keys.

Rebuild version-specific outputs from committed manifests:

```bash
python3 scripts/aggregate_version.py \
  --version benchmark-versions/v0.1.json \
  --results-manifest results/manifests/v0.1.json \
  --out-dir .
```

This regenerates `results/summaries/v0.1.json`, `leaderboard.md`,
`results.json`, and `badges/*.json`. Complete model rows are eligible for the
main ranking. Partial rows are labeled partial and excluded from complete-rank
comparisons.

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

There are two kinds of harness:

- `default`: the built-in fair harness. The model works through an OpenAI-compatible tool loop with Lean-native tools (`show_task`, `read_file`, `show_goal`, `definition_outline`, `tactic_sandbox`, `check_proof`, `try_tactics`, `search_declarations`); every tool call and conversation turn is logged in run artifacts. Native tool calls and JSON-encoded text tool calls are both supported.
- shell agent profiles (`grok-build`, `opencode`, `codex`, ... from `harness/agents/*.json`): an off-the-shelf coding agent CLI runs inside the workspace against a local metering proxy that measures token usage at the API boundary.

What every harness sees is identical and enforced, not promised:

- The workspace contains only public case files (contracts, specs, skeletons) plus the generic, contract-agnostic Grindset (`Attr`, `Monad`, `Core`, `Reach`, `ArithCore`) — the same lemma library the repo's own reference proofs compile against. `scripts/check_grindset_generic.py` (CI) forbids case-specific content in it.
- Hidden reference proofs (`Benchmark/Cases/*/Proofs.lean`) and `.env` are absent from the workspace, and the private `.lake` build dir is pruned to workspace sources, so they are not importable either.
- The verifier rebuilds the submission in its own private copy and rejects imports of any module the agent could not see, plus `sorry`/`admit`/`axiom` and theorem-statement changes.

Every harness receives the same generated `harness/TASK_SUMMARY.md` (target theorem, editable files, public files, check command, policy) and the same `./harness/check.sh`.

Operational notes: chat requests retry transient provider failures and log retry events in `conversations/*.jsonl`; task results carry `failure_class` so provider failures, no-tool loops, parse errors, unknown names, unsolved goals, and Lean timeouts are distinguishable. Provider switching lives in `.env` (`DEFAULT_HARNESS_PROVIDER=qwen|glm` reads `DEFAULT_HARNESS_<PROVIDER>_*` before the generic `DEFAULT_HARNESS_*` values); for small-context providers set `DEFAULT_HARNESS_NATIVE_TOOLS=0` and lower `DEFAULT_HARNESS_TOOL_RESULT_CHARS` / `DEFAULT_HARNESS_TASK_SUMMARY_CHARS`.

Budget profiles:

- `--budget quick`: CI-sized smoke budget.
- `--budget normal`: small comparison budget.
- `--budget deep`: long agent budget for real attempts.

```bash
# Run a single task with the default harness
python3 -m harness.cli run-task lido/vaulthub_locked/locked_funds_solvency --harness default

# Run a deeper fair agent attempt
python3 -m harness.cli run-task ethereum/deposit_contract_minimal/deposit_count --harness default --budget deep

# Run a full case with the default harness
./scripts/run_default_harness_group.sh lido/vaulthub_locked --max-attempts 2

# Run the full suite with the default harness
./scripts/run_default_harness_suite.sh --suite active --max-attempts 1

# Run a shell agent profile (grok-build, opencode, codex)
VERITY_ALLOW_HOST_GROK_AUTH=1 python3 -m harness.cli run-task ethereum/deposit_contract_minimal/deposit_count --harness grok-build --budget deep

# Compare runs across harnesses
python3 -m harness.cli run-task ethereum/deposit_contract_minimal/deposit_count --harness default
python3 -m harness.cli compare --runs results/runs/<default-fair-run> results/runs/<grok-build-run>
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

## Documentation

| Document | Description |
|----------|-------------|
| [harness/README.md](./harness/README.md) | Harness internals and agent integration |
| [docs/architecture/task-api.md](./docs/architecture/task-api.md) | Task contract and manifest format |
| [docs/architecture/results-publication.md](./docs/architecture/results-publication.md) | Versioned results data model for websites and downstream consumers |
