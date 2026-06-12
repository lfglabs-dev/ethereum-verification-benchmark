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

21 active cases, 124 active task manifests, and 8 backlog task manifests are drawn from real-world contracts. All active and backlog task manifests are currently runnable proof tasks with hidden reference proofs.

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
| `piku/fund_conservation` | Piku / Inverter oracle funding manager | 4 |
| `polygon/agglayer_bridge` | Polygon Agglayer bridge | 2 |
| `reserve/auction_price_band` | Reserve DTF | 4 |
| `rootstock/flyover_quote_lifecycle` | Rootstock Flyover quote lifecycle | 3 |
| `safe/owner_manager_reach` | Safe OwnerManager | 15 |
| `termmax/order_v2_buy_xt_single_segment` | TermMax Order V2 | 1 |
| `usual/dao_collateral` | Usual DaoCollateral | 5 |
| `wildcat/borrow_liquidity_safety` | Wildcat V2 | 1 |
| `zama/erc7984_confidential_token` | Zama / OpenZeppelin ERC-7984 | 12 |

Every runnable task includes a reference proof hidden from the agent during benchmarking. Case-level `proof_status: partial` means the broader case family is not fully complete; it does not imply that runnable per-task reference proofs are missing.

Coverage is strongest today for accounting, local state preservation, storage effects, linked-list ownership structures, and solvency invariants. Known thinner areas include reentrancy beyond modeled guards, oracle manipulation, governance/timelock properties, temporal or liveness properties, cross-contract compositional reasoning, cryptographic assumptions, and adversarial EVM-level behavior. See [docs/evaluated-surface.md](./docs/evaluated-surface.md) for the current evaluation surface.

---

## Results

[![Verity bench](https://img.shields.io/endpoint?url=https%3A%2F%2Fraw.githubusercontent.com%2Flfglabs-dev%2Fverity-benchmark%2Fbenchmark-results%2Fbadges%2Foverall.json)](https://github.com/lfglabs-dev/verity-benchmark/blob/benchmark-results/leaderboard.md)
[![MiniMax M3](https://img.shields.io/endpoint?url=https%3A%2F%2Fraw.githubusercontent.com%2Flfglabs-dev%2Fverity-benchmark%2Fbenchmark-results%2Fbadges%2Fbuiltin-smart.json)](https://github.com/lfglabs-dev/verity-benchmark/blob/benchmark-results/leaderboard.md)
[![Grok Build 0.1](https://img.shields.io/endpoint?url=https%3A%2F%2Fraw.githubusercontent.com%2Flfglabs-dev%2Fverity-benchmark%2Fbenchmark-results%2Fbadges%2Fgrok.json)](https://github.com/lfglabs-dev/verity-benchmark/blob/benchmark-results/leaderboard.md)
[![GLM 5 Turbo](https://img.shields.io/endpoint?url=https%3A%2F%2Fraw.githubusercontent.com%2Flfglabs-dev%2Fverity-benchmark%2Fbenchmark-results%2Fbadges%2Fbuiltin-fast.json)](https://github.com/lfglabs-dev/verity-benchmark/blob/benchmark-results/leaderboard.md)

We measure **cost to a verified proof**, not pass/fail alone. Each agent runs in an isolated
workspace with the reference proofs withheld; an independent verifier recompiles the submitted
file and checks the theorem statement is untouched. Token usage is metered at the API boundary
and priced at live [OpenRouter](https://openrouter.ai) rates. We evaluate two harness families
on identical tasks: the **builtin harness** (a minimal Lean-native tool loop: goal inspection,
declaration search, proof checking) and **generic coding agents** (opencode, codex, grok CLI)
given shell access to the same workspace.

Current results on a 5-task slice spanning four proof families, ranked by total cost
(full table, per-task data, and methodology notes in the
[leaderboard](https://github.com/lfglabs-dev/verity-benchmark/blob/benchmark-results/leaderboard.md)):

| Harness | Model | Verified | Median cost / proof | Total cost |
|---|---|---|---|---|
| builtin | MiniMax M3 | 5/5 | $0.24 | $1.49 |
| opencode | MiniMax M3 | 3/5 | $0.59 | $3.38 |
| codex | GPT-5.5 | 5/5 | ~$0.8–1.2 *(est.)* | ~$4–6 *(est.)* |
| opencode | GLM 5 Turbo | 5/5 | $0.39 | $5.29 |
| builtin | Grok Build 0.1 | 4/5 | $0.48 | $5.84 |
| builtin | GLM 5 Turbo | 5/5 | $1.52 | $7.39 |
| builtin | GPT-5.5 | 5/5 | $1.23 | $8.42 |
| grok CLI | Grok Build 0.1 | 4/5 | ~$0.5–5 *(est.)* | ~$3–25 *(est.)* |

Two observations so far, to be confirmed at larger scale:

1. **Given enough budget, every model proves almost everything.** The discriminating variable
   is cost: across models the spread is ~6× in total cost at equal success.
2. **Harness×model interaction is real.** More capable models (GPT-5.5, MiniMax M3) perform
   best inside the constrained builtin loop, while cheaper models (GLM 5 Turbo) do better as
   unconstrained shell agents — the structured tool protocol appears to help models that can
   exploit it and hinder those that cannot.

Estimates marked *(est.)* cover harnesses that expose no token telemetry (grok CLI) or only an
undecomposed total (codex); derivation is documented in the leaderboard. Results come from the
manually-dispatched [benchmark workflow](.github/workflows/benchmark.yml) (models, budgets,
task slice, and endpoint are dispatch inputs) and publish to the
[`benchmark-results`](https://github.com/lfglabs-dev/verity-benchmark/tree/benchmark-results)
branch; single-seed runs, so treat small deltas as noise.

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

- `default`: built-in Lean-tools harness. Its default `fair` mode is agent-first: no hardcoded local proof candidates, no theorem/task-name dispatch, and all model actions go through Lean-native tools logged in run artifacts.
- `grok-build`: Grok Build shell harness.

Default harness modes:

- `fair`: OpenAI-compatible tool loop with `show_task`, `read_file`, `show_goal`, `definition_outline`, `tactic_sandbox`, `check_proof`, `try_tactics`, and `search_declarations`. Fair workspaces ship only the generic, contract-agnostic Grindset modules (`Attr`, `Monad`, `Core`, `Reach`, `ArithCore` — enforced by `scripts/check_grindset_generic.py`); task skeletons import the trimmed `Benchmark.Grindset` umbrella so `grind_norm` is available to every agent. Workspaces and the verifier use private build dirs pruned to workspace sources, so hidden reference proofs and case-specific helper modules are not importable or in scope. Native tool calls and JSON-encoded text tool calls are both supported. This is the headline comparison mode.
- `fair+libs`: same agent-first loop as `fair`, but allows explicit inspection of the (generic-only) Grindset module files copied into the fair workspace.

Fair-mode chat requests retry transient provider failures by default and log retry events in `conversations/*.jsonl`. Provider-specific context-window hints such as `n_ctx` are opt-in through `DEFAULT_HARNESS_CONTEXT_TOKENS`. For small-context providers, set `DEFAULT_HARNESS_NATIVE_TOOLS=0` and lower `DEFAULT_HARNESS_TOOL_RESULT_CHARS` / `DEFAULT_HARNESS_TASK_SUMMARY_CHARS`; the harness will use compact JSON tool calls and keep full tool output in artifacts. Fair tools can search and read public Lean dependency files under `.lake`, while hidden proof files, GeneratedPreview, and `.env` remain blocked; Grindset module files are readable only in `fair+libs`.

Fair task results include `failure_class` so provider failures, no-tool loops, context loops, parse errors, unknown names, unsolved goals, Lean timeouts, and other Lean failures are distinguishable in run artifacts.

Provider switching is configured in `.env`. Set `DEFAULT_HARNESS_PROVIDER=qwen` or `DEFAULT_HARNESS_PROVIDER=glm` to make the default harness read `DEFAULT_HARNESS_QWEN_*` or `DEFAULT_HARNESS_GLM_*` values before the generic `DEFAULT_HARNESS_*` endpoint/model/key.

Fair-mode tools do not expose `Benchmark/Grindset/*` files by default. Set `DEFAULT_HARNESS_ALLOW_GRINDSET_TOOLS=1` only for explicit research runs that measure the value of generic Grindset helpers.

Both `default --mode fair` and `grok-build` receive the same generated `harness/TASK_SUMMARY.md` in each run workspace. It lists the target theorem, editable files, implementation/specification files, check command, and policy. Grok also gets the initial `./harness/check.sh` result in that summary so it does not spend turns rediscovering the first Lean failure.

Budget profiles:

- `--budget quick`: CI-sized smoke budget.
- `--budget normal`: small comparison budget.
- `--budget deep`: long agent budget for real attempts.

```bash
# Run a single task with the default harness
python3 -m harness.cli run-task lido/vaulthub_locked/locked_funds_solvency --harness default --mode fair

# Run a deeper fair agent attempt
python3 -m harness.cli run-task ethereum/deposit_contract_minimal/deposit_count --harness default --mode fair --budget deep

# Run a full case with the default harness
./scripts/run_default_harness_group.sh lido/vaulthub_locked --mode fair --max-attempts 2

# Run the full suite with the default harness
./scripts/run_default_harness_suite.sh --suite active --mode fair --max-attempts 1

# Run Grok Build
VERITY_ALLOW_HOST_GROK_AUTH=1 ./scripts/run_grok_build_group.sh ethereum/deposit_contract_minimal --max-turns 20
VERITY_ALLOW_HOST_GROK_AUTH=1 python3 -m harness.cli run-task ethereum/deposit_contract_minimal/deposit_count --harness grok-build --budget deep
./scripts/run_grok_build_suite.sh --suite active

# Compare runs across harnesses/modes
python3 -m harness.cli run-task ethereum/deposit_contract_minimal/deposit_count --harness default --mode fair
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
