# Harness

The benchmark now has two supported group harnesses:

- `default`: the built-in Lean-tools harness. It builds an isolated group workspace, tries deterministic local proof candidates, asks an OpenAI-compatible chat-completions API for proof bodies when needed, and verifies the final workspace independently.
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
- `group/lean_tools`: built-in proof-generation harness with local Lean candidates plus API fallback
- `group/shell`: shell-based coding-agent harness for Grok Build

Default harness API env:
- `DEFAULT_HARNESS_BASE_URL`
- `DEFAULT_HARNESS_MODEL`
- `DEFAULT_HARNESS_API_KEY`

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
- Without auth, the Grok runner writes a `harness_error` artifact instead of blocking on an interactive login prompt.

Useful commands:

```bash
python3 -m harness.cli list --suite active --unit group
python3 -m harness.cli run-task ethereum/deposit_contract_minimal/deposit_count --harness default --max-attempts 2 --keep-workspace
python3 -m harness.cli run-group ethereum/deposit_contract_minimal --harness default --max-attempts 2 --keep-workspace
python3 -m harness.cli run-suite --suite active --harness default --max-attempts 1
VERITY_ALLOW_HOST_GROK_AUTH=1 python3 -m harness.cli run-task ethereum/deposit_contract_minimal/deposit_count --harness grok-build --max-turns 20
python3 -m harness.cli run-group ethereum/deposit_contract_minimal --harness grok-build --dry-run --max-turns 20 --keep-workspace
python3 -m harness.cli run-suite --suite active --harness grok-build --dry-run
python3 -m harness.cli compare --runs results/runs/<default-run> results/runs/<grok-build-run>
python3 scripts/check_run_artifacts.py results/runs/<run_id>
python3 scripts/check_group_workspaces.py ethereum/deposit_contract_minimal
```
