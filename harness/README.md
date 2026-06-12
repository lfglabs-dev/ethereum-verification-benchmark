# Harness

The benchmark now has two supported group harnesses:

- `default`: the built-in Lean-tools harness. It builds an isolated group workspace, runs in `fair` or `fair+libs` mode, and verifies the final workspace independently.
- `grok-build`: the Grok Build shell harness. It gives Grok Build a generated group workspace and then verifies the produced proof files with the same independent verifier.

Task contract:
- fixed implementation files
- fixed specification files
- one editable proof file per target
- one theorem name per target

Main entrypoints:
- `python3 -m harness.cli list --suite active --unit group`
- `python3 -m harness.cli run-task <project/case/task> --harness default`
- `python3 -m harness.cli run-group <project/case> --harness default`
- `python3 -m harness.cli run-suite --suite active --harness default`
- `python3 -m harness.cli run-group <project/case> --harness grok-build`
- `python3 -m harness.cli run-suite --suite active --harness grok-build`
- `python3 -m harness.cli compare --runs results/runs/*`
- `scripts/run_default_harness_group.sh <project/case>`
- `scripts/run_default_harness_suite.sh --suite active`
- `scripts/run_grok_build_group.sh <project/case>`
- `scripts/run_grok_build_suite.sh --suite active`

Core files:
- `harness/manifests.py`: group/task manifest loader and scoring metadata
- `harness/workspace_builder.py`: generated group workspaces and file manifests
- `harness/verifier.py`: independent policy and Lean verifier
- `harness/cli.py`: group list/run-task/run-group/run-suite/compare CLI
- `harness/runners/lean_tools.py`: default OpenAI-compatible Lean-tools harness
- `harness/runners/grok_build.py`: Grok Build shell harness
- `harness/agents/default.json`: default harness profile metadata
- `harness/agents/grok-build.json`: Grok Build profile metadata

Runtime tracks:
- `group/lean_tools`: built-in proof-generation harness with selectable fair/fair+libs modes
- `group/shell`: shell-based coding-agent harness for Grok Build

Default harness modes:
- `fair`: the default, agent-first mode. It does not run hardcoded local proof candidates, heuristic grind candidates, or theorem/task-name dispatch. The repo Grindset is generic-only (no case-specific helper modules exist), and model proof patching does not add extra imports. The model interacts through an OpenAI-compatible tool loop with Lean-native tools: `show_task`, `read_file`, `show_goal`, `definition_outline`, `tactic_sandbox`, `check_proof`, `try_tactics`, and `search_declarations`; endpoints that return JSON-encoded tool calls as assistant text are accepted as a compatibility path. Assistant messages are written under `conversations/*.jsonl`; tool calls are written under `tool-calls/*.jsonl`; checked proof candidates are written under `attempts/*.lean` and summarized in `harness-response.json`. Missing remote API credentials produce a `missing_credentials` artifact instead of accidentally comparing against a non-agent path.
- `fair+libs`: same fair agent loop, with the generic Grindset module files visible to read/search tools.

Task briefing:
- Every task/group workspace contains `harness/TASK_SUMMARY.md`.
- The summary is shared by fair default and Grok Build and includes target theorem names, editable files, implementation/specification files, the exact `./harness/check.sh` command, policy, and current editable theorem skeletons.
- Grok Build appends the initial check result to the summary before the shell agent starts. The fair default agent receives the same summary through `show_task`.
- Fair-mode `definition_outline`, `search_declarations`, and `read_file` can inspect public Lean dependency files under `.lake`, while hidden proof files, GeneratedPreview, `.env`, and Grindset remain blocked by default.
- Fair task results include `failure_class`, distinguishing provider/context failures, no-tool loops, context loops, proof parse errors, unknown names, unsolved goals, Lean timeouts, and other Lean failures.

Budget profiles:
- `quick`: `max_attempts=4`, `max_tool_calls=40`, `max_turns=20`, `grok_timeout_seconds=900`.
- `normal`: `max_attempts=16`, `max_tool_calls=120`, `max_turns=50`, `grok_timeout_seconds=2400`.
- `deep`: `max_attempts=48`, `max_tool_calls=400`, `max_turns=100`, `grok_timeout_seconds=7200`.
- Explicit `--max-attempts`, `--max-tool-calls`, `--max-turns`, or `--grok-timeout-seconds` override the selected profile.

Default harness API env:
- `DEFAULT_HARNESS_BASE_URL`
- `DEFAULT_HARNESS_MODEL`
- `DEFAULT_HARNESS_API_KEY`
- `DEFAULT_HARNESS_REQUEST_TIMEOUT_SECONDS`
- `DEFAULT_HARNESS_REQUEST_RETRIES`
- `DEFAULT_HARNESS_REQUEST_RETRY_BACKOFF_SECONDS`
- `DEFAULT_HARNESS_MAX_TOOL_CALLS`
- `DEFAULT_HARNESS_MAX_RESPONSE_TOKENS`
- `DEFAULT_HARNESS_NATIVE_TOOLS`
- `DEFAULT_HARNESS_TOOL_RESULT_CHARS`
- `DEFAULT_HARNESS_TASK_SUMMARY_CHARS`
- `DEFAULT_HARNESS_MAX_NON_PROOF_TOOL_CALLS`
- `DEFAULT_HARNESS_ALLOW_GRINDSET_TOOLS` for explicit research runs with
  generic Grindset helper visibility; default fair comparisons keep this off
- `DEFAULT_HARNESS_CONTEXT_TOKENS` if the provider supports an `n_ctx` request hint
- `DEFAULT_HARNESS_TOKEN_BUDGET` to stop a task after N completion tokens (0 = unlimited);
  per-task and aggregate `usage` is reported in `harness-response.json` and `run.json`
- `DEFAULT_HARNESS_WARM_BUILD_TIMEOUT_SECONDS` for the one-time dependency warm build
  the fair runner performs per target module before the agent loop starts (default 1800)
- `DEFAULT_HARNESS_HTTP_USER_AGENT` to override the request User-Agent (default
  `verity-benchmark-harness/1.0`; some proxies reject the Python default UA)
- `DEFAULT_HARNESS_CHECK_MODE`: `file` (default) checks the editable proof file with
  `lake env lean` (seconds; falls back to `lake build` on dependency-graph errors),
  `module` always runs the full `lake build <target>`
- `DEFAULT_HARNESS_STUCK_NUDGE`: `1` (default) appends a change-strategy nudge when a
  proof attempt repeats the same error signature; failed attempts also carry a
  failure-class `hint` (unsolved goals, unknown name, parse, type, timeout)

Fair-mode behavior notes:
- Before any agent request, the runner builds each target module once so agent-visible
  Lean check timeouts measure proof elaboration rather than cold dependency builds.
  Run `lake exe cache get && lake build` on the host before benchmarking.
- `check_proof`/`try_tactics` accept either a tactic body (placed under `:= by` with
  relative indentation preserved verbatim) or a complete Lean file with imports,
  helper lemmas, and the target theorem. Submissions that change the target theorem
  statement are rejected with `statement_mismatch` feedback.
- `show_goal` does not consume the non-proof tool budget.

Local runtime configuration:
- Copy `.env.example` to `.env`.
- Put local provider keys and model settings in `.env`.
- `.env` is ignored by git and loaded by `harness.cli` before runner startup.
- Existing process environment variables take precedence over values in `.env`.
- To switch between configured providers without editing the generic endpoint,
  set `DEFAULT_HARNESS_PROVIDER=qwen` or `DEFAULT_HARNESS_PROVIDER=glm`.
  The selected profile reads `DEFAULT_HARNESS_QWEN_*` or
  `DEFAULT_HARNESS_GLM_*` values first, then falls back to the generic
  `DEFAULT_HARNESS_*` values.

Compatibility env still accepted by the default harness:
- `GAZELLA_BASE_URL`
- `GAZELLA_MODEL`
- `GAZELLA_API_KEY`
- `OPENAI_API_KEY`

Grok auth:
- CI/local automation should set `GROK_CODE_XAI_API_KEY`.
- Host `~/.grok/auth.json` is not copied unless `VERITY_ALLOW_HOST_GROK_AUTH=1`.
- Without usable auth, the Grok runner writes a `harness_error` artifact instead of blocking on an interactive login prompt. It preflights `grok models` inside the isolated run home so stale copied host auth fails quickly.

Useful commands:

```bash
python3 -m harness.cli list --suite active --unit group
python3 -m harness.cli run-task ethereum/deposit_contract_minimal/deposit_count --harness default --max-attempts 2 --keep-workspace
python3 -m harness.cli run-task ethereum/deposit_contract_minimal/deposit_count --harness default --budget deep
python3 -m harness.cli run-group ethereum/deposit_contract_minimal --harness default --max-attempts 2 --keep-workspace
python3 -m harness.cli run-suite --suite active --harness default --max-attempts 1
VERITY_ALLOW_HOST_GROK_AUTH=1 python3 -m harness.cli run-task ethereum/deposit_contract_minimal/deposit_count --harness grok-build --max-turns 20
VERITY_ALLOW_HOST_GROK_AUTH=1 python3 -m harness.cli run-task ethereum/deposit_contract_minimal/deposit_count --harness grok-build --budget deep
python3 -m harness.cli run-group ethereum/deposit_contract_minimal --harness grok-build --dry-run --max-turns 20 --keep-workspace
python3 -m harness.cli run-suite --suite active --harness grok-build --dry-run
python3 -m harness.cli compare --runs results/runs/<default-fair-run> results/runs/<grok-build-run>
python3 scripts/check_run_artifacts.py results/runs/<run_id>
python3 scripts/check_group_workspaces.py ethereum/deposit_contract_minimal
```
