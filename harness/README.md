# Harness

The benchmark now has two supported group harnesses:

- `default`: the built-in Lean-tools harness. It builds an isolated group workspace, runs in `fair`, `tuned`, or `legacy` mode, and verifies the final workspace independently.
- `grok-build`: the Grok Build shell harness. It gives Grok Build a generated group workspace and then verifies the produced proof files with the same independent verifier.

Task contract:
- fixed implementation files
- fixed specification files
- one editable proof file per target
- one theorem name per target

Main entrypoints:
- `python3 -m harness.cli list --suite active --unit group`
- `python3 -m harness.cli run-task <project/case/task> --harness default --mode fair`
- `python3 -m harness.cli run-group <project/case> --harness default --mode fair`
- `python3 -m harness.cli run-suite --suite active --harness default --mode fair`
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
- `group/lean_tools`: built-in proof-generation harness with selectable fair/tuned/legacy modes
- `group/shell`: shell-based coding-agent harness for Grok Build

Default harness modes:
- `fair`: the default, agent-first mode. It does not run hardcoded local proof candidates, heuristic grind candidates, or theorem/task-name dispatch. Its workspace excludes group-specific Grindset helper modules, and model proof patching does not add broad `Benchmark.Grindset` imports. The model interacts through an OpenAI-compatible tool loop with Lean-native tools: `show_task`, `read_file`, `show_goal`, `check_proof`, `try_tactics`, and `search_declarations`; endpoints that return JSON-encoded tool calls as assistant text are accepted as a compatibility path. Assistant messages are written under `conversations/*.jsonl`; tool calls are written under `tool-calls/*.jsonl`; checked proof candidates are written under `attempts/*.lean` and summarized in `harness-response.json`. Missing remote API credentials in fair/tuned modes produce a `missing_credentials` artifact instead of accidentally comparing against a non-agent path.
- `tuned`: generic heuristic/API comparison mode without hardcoded local proof candidates, broad Grindset import patching, or group-specific Grindset helper modules.
- `legacy`: compatibility mode for the previous local-candidate and group-specific Grindset behavior. Use this only as an upper-bound/debug signal, not as the headline comparison.

Task briefing:
- Every task/group workspace contains `harness/TASK_SUMMARY.md`.
- The summary is shared by fair default and Grok Build and includes target theorem names, editable files, implementation/specification files, the exact `./harness/check.sh` command, policy, and current editable theorem skeletons.
- Grok Build appends the initial check result to the summary before the shell agent starts. The fair default agent receives the same summary through `show_task`.

Budget profiles:
- `quick`: `max_attempts=1`, `max_tool_calls=24`, `max_turns=20`, `grok_timeout_seconds=900`.
- `normal`: `max_attempts=4`, `max_tool_calls=80`, `max_turns=50`, `grok_timeout_seconds=2400`.
- `deep`: `max_attempts=12`, `max_tool_calls=200`, `max_turns=100`, `grok_timeout_seconds=7200`.
- Explicit `--max-attempts`, `--max-tool-calls`, `--max-turns`, or `--grok-timeout-seconds` override the selected profile.

Default harness API env:
- `DEFAULT_HARNESS_BASE_URL`
- `DEFAULT_HARNESS_MODEL`
- `DEFAULT_HARNESS_API_KEY`
- `DEFAULT_HARNESS_REQUEST_TIMEOUT_SECONDS`
- `DEFAULT_HARNESS_MAX_TOOL_CALLS`
- `DEFAULT_HARNESS_MAX_RESPONSE_TOKENS`

Local runtime configuration:
- Copy `.env.example` to `.env`.
- Put local provider keys and model settings in `.env`.
- `.env` is ignored by git and loaded by `harness.cli` before runner startup.
- Existing process environment variables take precedence over values in `.env`.

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
python3 -m harness.cli run-task ethereum/deposit_contract_minimal/deposit_count --harness default --mode fair --max-attempts 2 --keep-workspace
python3 -m harness.cli run-task ethereum/deposit_contract_minimal/deposit_count --harness default --mode fair --budget deep
python3 -m harness.cli run-group ethereum/deposit_contract_minimal --harness default --mode tuned --max-attempts 2 --keep-workspace
python3 -m harness.cli run-suite --suite active --harness default --mode fair --max-attempts 1
VERITY_ALLOW_HOST_GROK_AUTH=1 python3 -m harness.cli run-task ethereum/deposit_contract_minimal/deposit_count --harness grok-build --max-turns 20
VERITY_ALLOW_HOST_GROK_AUTH=1 python3 -m harness.cli run-task ethereum/deposit_contract_minimal/deposit_count --harness grok-build --budget deep
python3 -m harness.cli run-group ethereum/deposit_contract_minimal --harness grok-build --dry-run --max-turns 20 --keep-workspace
python3 -m harness.cli run-suite --suite active --harness grok-build --dry-run
python3 -m harness.cli compare --runs results/runs/<default-fair-run> results/runs/<default-tuned-run> results/runs/<grok-build-run>
python3 scripts/check_run_artifacts.py results/runs/<run_id>
python3 scripts/check_group_workspaces.py ethereum/deposit_contract_minimal
```
