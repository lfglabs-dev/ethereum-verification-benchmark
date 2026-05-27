# Harness Audit 2026-05-26

Objective: implement the group-aware benchmark harness from `PLAN.md`, test it with Grok Build and the Gazella custom harness, report issues, improve, and repeat until 2026-05-26 17:00 Lisbon.

## Implemented Evidence

- Manifest layer: `harness/manifests.py`, explicit `[[groups]]` support in `benchmark.toml`, active inventory of 16 groups and 99 runnable tasks.
- Workspace layer: `harness/workspace_builder.py`, `workspace-manifest.json`, hidden-proof leak checks, dependency-cache declaration, and `scripts/check_group_workspaces.py`.
- Verifier layer: `harness/verifier.py`, independent copy-and-build verification, target scoring, hidden import/theorem mismatch/placeholder policy checks, and verifier temp cleanup.
- Harness layer: Grok Build runner, shell-agent runner, Gazella Lean-tool runner, normalized profiles under `harness/agents/`, and wrapper scripts for Grok/Gazella group and suite runs.
- Reporting layer: run-level `run.json`, `report.md`, suite aggregate artifacts, comparison by capability track, and stricter artifact validation.
- Sandbox layer: Grok strict invocation, shell fake-home isolation, local/Podman smoke command, and Podman policy reporting.

## Verification Evidence

- `./scripts/check.sh` passed after the final verifier cleanup change.
- `python3 -m harness.cli list --suite active --unit group` reports 16 groups.
- `python3 -m harness.cli list --suite active --unit task` reports 99 tasks.
- `python3 scripts/check_run_artifacts.py` validates representative Grok, Gazella, and suite artifacts.
- `python3 -m harness.sandbox_runner smoke --executor podman` reports `skipped` because Podman is not installed, while still emitting the configured isolation policy.
- `grok --version` reports `grok 0.1.211`; `grok models` reports unauthenticated with default model `grok-build`.
- Gazella endpoint smoke succeeds against `https://spark-de79.gazella-vector.ts.net/v1`.

## Representative Artifacts

- Grok dry active-suite aggregate: `results/runs/20260526T153528-grok-build-suite-active/run.json`
- Grok unauthenticated task run: `results/runs/20260526T150518-grok-build-ethereum__deposit_contract_minimal__deposit_count/run.json`
- Default harness live task run recorded on 2026-05-26.
- Default harness live group run recorded on 2026-05-26.

## Remaining Blockers

- Grok Build cannot be tested as a live solving agent until `GROK_CODE_XAI_API_KEY` or explicitly approved per-run auth is available.
- Rootless Podman cannot be executed on this machine because `podman` is not installed.
- Claude Code, Codex, and OpenCode live baselines need explicit non-interactive auth compatible with isolated per-run `HOME`.
- Gazella runs reach the endpoint and produce candidates, but current proof quality remains 0/5 on `ethereum/deposit_contract_minimal`; failures include unsolved Verity storage branch goals and invented unavailable lemmas.

## Next Improvements

- Add structured Lean goal inspection for the Gazella harness rather than relying on prompt-only retries.
- Generate public-information proof skeletons for common Verity storage-update branches.
- Add CI with rootless Podman once available.
- Run the planned Grok easy/hard group sequence and active suite once authentication is provided.
