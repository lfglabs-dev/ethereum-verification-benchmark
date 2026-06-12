# Harness Architecture Audit, 2026-05-27

Objective: audit the benchmark harness after the fair agent-first default harness work, remove solution-shaped default behavior, fix concrete artifact and fairness gaps, and record comparison artifacts for default fair mode and Grok Build.

## Fairness Boundary

Default `fair` mode is the auditable evaluation surface for the built-in Lean-tools harness.

- It does not run `_local_tactic_candidates` or `_heuristic_tactic_candidates`.
- It does not branch on benchmark, group, task, theorem, or known proof names in the solving loop.
- It exposes only generic Lean-native tools: `show_task`, `read_file`, `show_goal`, `check_proof`, `try_tactics`, and `search_declarations`.
- It writes assistant messages to `conversations/*.jsonl`, tool calls to `tool-calls/*.jsonl`, proof candidates to `attempts/*.lean`, final submitted files to `submitted/`, and verifier output to `verifier/verifier.json`.
- Its workspace manifest records `tool_policy.include_group_grindset=false`.
- Its workspace excludes group-specific Grindset helper modules such as `Benchmark/Grindset/Arith.lean`, `Kleros.lean`, `Reserve.lean`, `Cork.lean`, and `Paladin.lean`.
- Fair proof patching no longer adds broad `import Benchmark.Grindset`; an agent must use imports already present in the editable file or public generic modules available in the workspace.

Comparison modes remain available outside the fair surface:

- `tuned` preserves the previous local candidate and heuristic path for regression comparison.
- `legacy` is a compatibility alias for that same previous default behavior.
- `grok-build` is a shell-agent track and is compared by artifact schema and verifier result, not by claiming the same capability track.

## Audit Findings And Changes

- Overfitting risk: the default runner still contains theorem-name local candidates for tuned/legacy comparison, but fair mode bypasses them completely.
- Helper leak risk: the workspace builder previously copied all `Benchmark/Grindset/*.lean` helper modules into every group workspace and generated a group-specific umbrella import. Fair mode now builds with `include_group_grindset=false`, copying only generic Grindset support modules.
- Import leak risk: model proof patching previously inserted broad `Benchmark.Grindset`. It now patches only the submitted proof body.
- Comparison compatibility: tuned/legacy API fallback keeps the previous broad `Benchmark.Grindset` import behavior, while fair mode uses a separate no-import response patcher.
- Tool-limit risk: `max_tool_calls` now limits executed tool calls, records skipped overflow calls, and writes `duration_seconds` for each executed tool call. `max_attempts` is also enforced across multiple proof-check tool calls in the same model response. Proof-attempt records include Lean check duration.
- Provider latency risk: default harness chat requests now honor `DEFAULT_HARNESS_REQUEST_TIMEOUT_SECONDS` / `GAZELLA_REQUEST_TIMEOUT_SECONDS`, preserving the previous 180-second default while allowing faster failure-mode checks for stuck endpoints.
- Tool-call compatibility: fair mode accepts function-call arguments returned either as JSON strings or already-decoded objects.
- Provider compatibility: fair mode also accepts JSON-encoded text tool calls for OpenAI-compatible endpoints that do not emit native `tool_calls` fields, while still routing all actions through the same generic tool executor.
- Tool error handling: invalid `read_file` paths and non-UTF-8 file reads are returned as structured tool errors instead of escaping as harness exceptions.
- Fair conversation auditability: assistant messages and usage are logged per task under `conversations/*.jsonl`, including request failures. Fair task summaries in `harness-response.json` include `tool_calls_executed`, `tool_log`, and `conversation_log`.
- Artifact clarity: default task/group run artifacts now include `started_at`; run reports distinguish `run mode` from `harness mode`; suite child summaries and comparison rows now include harness mode.
- Grok observability: Grok Build request artifacts now include `max_turns` and `auth_mode`.
- Grok artifact correctness: `grok-output.json` is now always valid JSON; malformed or non-JSON stdout is wrapped as `raw_stdout`.
- Verifier contract clarity: Grok prompts and `.grok/rules.md` no longer permit `Benchmark/User` helper files, because the verifier copies only declared editable files.
- Workspace isolation clarity: forbidden proof-file checks now cover `Benchmark/Cases/**/*Proofs.lean`, matching the copier's broader exclusion.
- Verifier import policy: imports of any `Benchmark.Cases.*` module whose final component ends in `Proofs` are rejected, including `OpenProofs` and multi-module import lines.
- Task workspace helper selection: filtered task runs now select comparison-mode Grindset helpers by the base `project/case` id, fixing tuned task runs such as `lido/vaulthub_locked/ceildiv_sandwich`.
- Comparison workspace reduction: non-fair workspaces now copy only generic Grindset support plus the one group-specific helper imported by that group, not all helper/test modules.
- Agent-visible metadata hygiene: `harness/TASKS.json`, workspace manifests, and Grok prompts no longer expose `reference_solution` module/declaration names.
- Public prompt clarity: `harness/PROMPT.md` now distinguishes shell agents that edit full files from tool-loop agents that submit tactic bodies, and `docs/architecture/runtime-modes.md` maps the current concrete harness modes onto the older runtime terminology.
- Validation gap: added `scripts/check_fair_harness_policy.py` and `scripts/check_harness_helpers.py`, wired them into `scripts/check.sh`, added harness profile JSON syntax checks, and extended `scripts/check_run_artifacts.py` so fair default artifacts must record `include_group_grindset=false` and `max_tool_calls`; task/group artifacts must include submitted files; default suite artifacts must aggregate child runs from the same mode.
- Artifact validator robustness: malformed required JSON sidecars are now reported as normal validation errors instead of crashing the artifact checker.
- Profile metadata: `harness/agents/default.json` now advertises the default `max_attempts` and `max_tool_calls` values used by the runner.

## Validation

Commands run after the fair workspace change:

```bash
python3 scripts/check_fair_harness_policy.py
python3 scripts/check_harness_helpers.py
python3 -m py_compile harness/*.py harness/runners/*.py scripts/check_fair_harness_policy.py scripts/check_harness_helpers.py
python3 -m harness.cli run-task ethereum/deposit_contract_minimal/deposit_count --harness default --dry-run
python3 -m harness.cli run-task ethereum/deposit_contract_minimal/deposit_count --harness default --mode tuned --dry-run
python3 -m harness.cli run-task ethereum/deposit_contract_minimal/deposit_count --harness grok-build --dry-run
python3 scripts/check_run_artifacts.py results/runs/20260527T173326-default-fair-ethereum__deposit_contract_minimal__deposit_count
python3 scripts/check_run_artifacts.py results/runs/20260527T173342-default-tuned-ethereum__deposit_contract_minimal__deposit_count
python3 scripts/check_run_artifacts.py results/runs/20260527T173326-grok-build-ethereum__deposit_contract_minimal__deposit_count
python3 -m harness.cli compare --runs results/runs/20260527T173326-default-fair-ethereum__deposit_contract_minimal__deposit_count results/runs/20260527T173342-default-tuned-ethereum__deposit_contract_minimal__deposit_count results/runs/20260527T173326-grok-build-ethereum__deposit_contract_minimal__deposit_count
DEFAULT_HARNESS_BASE_URL=http://127.0.0.1:8766/v1 python3 -m harness.cli run-task ethereum/deposit_contract_minimal/deposit_count --harness default --max-attempts 1 --max-tool-calls 3
python3 scripts/check_run_artifacts.py results/runs/20260527T174642-default-fair-ethereum__deposit_contract_minimal__deposit_count
PATH=<fake-grok-dir>:$PATH GROK_CODE_XAI_API_KEY=dummy python3 -m harness.cli run-task ethereum/deposit_contract_minimal/deposit_count --harness grok-build --max-turns 1
python3 scripts/check_run_artifacts.py results/runs/20260527T174320-grok-build-ethereum__deposit_contract_minimal__deposit_count
python3 scripts/check_group_workspaces.py ethereum/deposit_contract_minimal
python3 -m harness.cli run-suite --suite active --harness default --dry-run
python3 -m harness.cli run-suite --suite active --harness grok-build --dry-run
python3 scripts/check_run_artifacts.py results/runs/20260527T173437-default-fair-suite-active results/runs/20260527T173437-grok-build-suite-active
python3 scripts/check_run_artifacts.py <20 child artifacts from results/runs/20260527T173437-default-fair-suite-active/run.json>
python3 scripts/check_run_artifacts.py <20 child artifacts from results/runs/20260527T173437-grok-build-suite-active/run.json>
python3 -m harness.cli run-task lido/vaulthub_locked/ceildiv_sandwich --harness default --mode tuned --max-attempts 0
python3 scripts/check_run_artifacts.py results/runs/20260527T172257-default-tuned-lido__vaulthub_locked__ceildiv_sandwich
python3 -m harness.cli run-task reserve/auction_price_band/price_upper_bound --harness default --mode tuned --max-attempts 0
python3 -m harness.cli run-task kleros/sortition_trees/node_id_bijection --harness default --mode tuned --max-attempts 0
python3 -m harness.cli run-task cork/pool_solvency/solvency_preserved --harness default --mode tuned --max-attempts 0
python3 scripts/check_run_artifacts.py results/runs/20260527T172543-default-tuned-reserve__auction_price_band__price_upper_bound results/runs/20260527T172554-default-tuned-kleros__sortition_trees__node_id_bijection results/runs/20260527T172606-default-tuned-cork__pool_solvency__solvency_preserved
VERITY_RUN_FULL_TASK_SWEEP=1 ./scripts/check.sh
./scripts/check.sh
DEFAULT_HARNESS_REQUEST_TIMEOUT_SECONDS=5 python3 -m harness.cli run-task ethereum/deposit_contract_minimal/deposit_count --harness default --max-attempts 1 --max-tool-calls 4
python3 scripts/check_run_artifacts.py results/runs/20260528T081935-default-fair-ethereum__deposit_contract_minimal__deposit_count
DEFAULT_HARNESS_REQUEST_TIMEOUT_SECONDS=5 python3 -m harness.cli run-task ethereum/deposit_contract_minimal/deposit_count --harness default --mode tuned --max-attempts 1
python3 scripts/check_run_artifacts.py results/runs/20260528T081957-default-tuned-ethereum__deposit_contract_minimal__deposit_count
python3 -m harness.cli compare --runs results/runs/20260528T081935-default-fair-ethereum__deposit_contract_minimal__deposit_count results/runs/20260528T081957-default-tuned-ethereum__deposit_contract_minimal__deposit_count
```

Observed results:

| Run | Harness | Mode | Status | Score | Failure mode | Duration |
|---|---|---|---|---:|---|---:|
| `results/runs/20260527T173326-default-fair-ethereum__deposit_contract_minimal__deposit_count` | default | fair | dry_run | 0/1 | forbidden_placeholder | 0.136s |
| `results/runs/20260527T173342-default-tuned-ethereum__deposit_contract_minimal__deposit_count` | default | tuned | dry_run | 0/1 | forbidden_placeholder | 0.133s |
| `results/runs/20260527T173326-grok-build-ethereum__deposit_contract_minimal__deposit_count` | grok-build | n/a | dry_run | 0/1 | forbidden_placeholder | 0.148s |

Dry-run comparison intentionally leaves the placeholder proof in place; the verifier failure is the expected artifact and policy check for this smoke subset. `harness.cli compare` reports `mode=fair` and `mode=tuned` for the default runs and `mode=null` for the Grok Build run.

The non-dry local fake-endpoint fair run `results/runs/20260527T174642-default-fair-ethereum__deposit_contract_minimal__deposit_count` validated the HTTP tool loop without external credentials. It returned synthetic `show_task`, invalid `read_file`, and `check_proof` tool calls, wrote `conversations/deposit_count.jsonl`, `tool-calls/deposit_count.jsonl`, and `attempts/deposit_count-fair-1-check_proof.lean`, recorded the invalid file path as a structured tool error, and failed 0/1 as expected because the synthetic `trivial` proof did not solve the task.

The non-dry fake-Grok run `results/runs/20260527T174320-grok-build-ethereum__deposit_contract_minimal__deposit_count` validated Grok Build artifact normalization without real Grok credentials. A fake `grok` executable returned plain stdout; `grok-output.json` wrapped it as `{"raw_stdout": ...}`, and `scripts/check_run_artifacts.py` accepted the artifact.

Suite aggregation dry runs also validated:

| Run | Harness | Mode | Groups | Score | Status |
|---|---|---|---:|---:|---|
| `results/runs/20260527T173437-default-fair-suite-active` | default | fair | 20 | 1/121 | completed_with_failures |
| `results/runs/20260527T173437-grok-build-suite-active` | grok-build | n/a | 20 | 1/121 | completed_with_failures |

Comparison-mode task run after the workspace-helper fix:

| Run | Harness | Mode | Task | Score | Status |
|---|---|---|---|---:|---|
| `results/runs/20260527T172257-default-tuned-lido__vaulthub_locked__ceildiv_sandwich` | default | tuned | `lido/vaulthub_locked/ceildiv_sandwich` | 1/1 | passed |
| `results/runs/20260527T172543-default-tuned-reserve__auction_price_band__price_upper_bound` | default | tuned | `reserve/auction_price_band/price_upper_bound` | 1/1 | passed |
| `results/runs/20260527T172554-default-tuned-kleros__sortition_trees__node_id_bijection` | default | tuned | `kleros/sortition_trees/node_id_bijection` | 1/1 | passed |
| `results/runs/20260527T172606-default-tuned-cork__pool_solvency__solvency_preserved` | default | tuned | `cork/pool_solvency/solvency_preserved` | 1/1 | passed |

Live configured-endpoint smoke on 2026-05-28:

| Run | Harness | Mode | Task | Score | Status | Notes |
|---|---|---|---|---:|---|---|
| `results/runs/20260528T081935-default-fair-ethereum__deposit_contract_minimal__deposit_count` | default | fair | `ethereum/deposit_contract_minimal/deposit_count` | 0/1 | request timeout | `DEFAULT_HARNESS_REQUEST_TIMEOUT_SECONDS=5` returned a valid failed artifact in 5.675s with no tool calls executed. |
| `results/runs/20260528T081957-default-tuned-ethereum__deposit_contract_minimal__deposit_count` | default | tuned | `ethereum/deposit_contract_minimal/deposit_count` | 1/1 | passed | Solved via `local:ethereum_deposit_branch_simp`, confirming comparison mode still preserves the previous local candidate path. |

This live comparison is evidence that the new timeout control works and that tuned-mode compatibility remains intact. It is not evidence that the fair tool-loop model can solve this task, because the configured endpoint timed out before returning a tool call.

The full reference-task sweep also completed successfully under `VERITY_RUN_FULL_TASK_SWEEP=1 ./scripts/check.sh`, generating active and backlog `results/tasks/*.json` artifacts through the final Uniswap backlog tasks.

Fair workspace spot check:

```json
{
  "tool_policy": {
    "include_group_grindset": false
  },
  "grindset_files": [
    "Benchmark/Grindset/Attr.lean",
    "Benchmark/Grindset/Core.lean",
    "Benchmark/Grindset/Monad.lean",
    "Benchmark/Grindset/Reach.lean"
  ]
}
```

For `lido/vaulthub_locked`, the fair workspace contains 36 manifest files and 5 Grindset files; the comparison workspace with the needed group helper contains 37 manifest files and 6 Grindset files. Before this audit, comparison workspaces copied 13 Grindset files, including helper/test modules unrelated to the group.

## Remaining Risks

- Live fair-mode solving quality depends on OpenAI-compatible tool-call support from the configured endpoint.
- `tuned` and `legacy` intentionally retain local theorem-specific candidates and must not be used as fair evaluation modes.
- Full live Grok Build solving requires configured Grok authentication; dry-run artifacts validate harness plumbing and verifier policy but not agent capability.
- The configured fair-mode endpoint timed out during the 2026-05-28 live smoke before returning a tool call, so live fair capability comparison remains endpoint-blocked rather than harness-blocked.

## Objective Checklist

| Requirement | Evidence | Status |
|---|---|---|
| Audit overfitting risk | Fair mode bypasses local theorem-specific candidates; `scripts/check_fair_harness_policy.py` statically checks the fair loop does not call local/heuristic candidate functions or contain branch-shaped benchmark/group/theorem text. | covered |
| Remove unnecessary solution-shaped complexity from fair mode | Fair workspace uses `include_group_grindset=false`; fair proof patching no longer adds broad `Benchmark.Grindset`; Grok helper-file allowance removed; agent-visible metadata omits `reference_solution`. | covered |
| Fix concrete correctness bugs | Fixed tool-call/proof-attempt cap enforcement, decoded-object tool arguments, always-valid `grok-output.json`, missing default `started_at`, and misleading full-file prompt text. | covered |
| Improve Lean-native tools only generically | Fair tools remain generic task/file/goal/proof-check/search operations; no benchmark-specific tool branching added. | covered |
| Artifact auditability | Run artifacts include request/response, workspace manifest, submitted files, stdout/stderr, verifier output, timing, mode, and tool/proof attempt logs for live fair runs; this was exercised with a local fake OpenAI-compatible endpoint. | covered |
| Verifier weakness checks | `scripts/check_verifier_policy.py` and `scripts/check_run_artifacts.py` run in `scripts/check.sh`; artifact validator now enforces fair workspace policy and default suite child mode consistency, and reports malformed JSON cleanly. | covered |
| Performance/complexity | Fair Lido workspace drops from 44 files/13 Grindset files to 36 files/5 Grindset files. | covered |
| Documentation | `harness/README.md`, top-level `README.md`, `harness/PROMPT.md`, `docs/architecture/runtime-modes.md`, and this audit document describe modes and fairness boundaries. | covered |
| Before/after and cross-harness comparison | Representative task and suite dry-run artifacts for default fair/tuned and Grok Build are listed above. | dry-run only |
| CI passes | `./scripts/check.sh` and `VERITY_RUN_FULL_TASK_SWEEP=1 ./scripts/check.sh` passed after the latest changes. | covered |

Dry-run comparison is sufficient for harness plumbing and verifier-policy regression checks, but it is not evidence of live agent solving quality.
