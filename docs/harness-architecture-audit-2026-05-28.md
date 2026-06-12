# Harness Architecture Audit - 2026-05-28

Objective: keep headline benchmark comparisons focused on solver capability, not hidden benchmark-specific helper knowledge.

Changes in this audit:

- Added shared `harness/TASK_SUMMARY.md` generation for every task/group workspace.
- Fed the shared summary to both `default` and `grok-build`.
- Added `quick`, `normal`, and `deep` budget profiles so long agent runs are explicit and reproducible.
- Added Grok `timeout_seconds` handling, timeout artifacts, stdout/stderr preservation, and editable-file diffs.
- Added a Grok initial `./harness/check.sh` pass before the shell agent starts and appended the compact result to `TASK_SUMMARY.md`.
- Added a non-interactive Grok auth preflight so stale host auth fails in seconds instead of entering OAuth during a benchmark run.
- Made fair default runs without remote credentials return a `missing_credentials` artifact unless the endpoint is localhost/no-auth.
- Kept group-specific Grindset helpers outside fair and tuned workspaces. Legacy remains available as a debugging/upper-bound mode for the previous local-candidate behavior.

Fairness boundary:

- Fair mode must not branch on benchmark, group, task, theorem, or known proof names.
- Fair mode must not import hidden Proofs modules or Benchmark/GeneratedPreview.
- Fair mode must not use group-specific Grindset helpers.
- The shared task summary may expose public task metadata, public file paths, editable theorem skeletons, and Lean diagnostics from the public check command.
- Tuned may use generic heuristic/API fallback, but not hardcoded local candidates or group-specific Grindset helpers.
- Legacy may use local candidates or helper libraries, but its results should be reported separately from fair comparisons.

Recommended comparisons:

```bash
python3 -m harness.cli run-task ethereum/deposit_contract_minimal/deposit_count --harness default --budget normal
VERITY_ALLOW_HOST_GROK_AUTH=1 python3 -m harness.cli run-task ethereum/deposit_contract_minimal/deposit_count --harness grok-build --budget normal
python3 -m harness.cli compare --runs results/runs/<default-fair-run> results/runs/<grok-build-run>
```

Use `--budget deep` when inspecting whether either agent is still making useful progress under a larger token and wall-clock budget.

Measurement notes from this pass:

- The current workspace had no `.env` and no default-harness API key. `default` and `default --mode tuned` now finish quickly with `missing_credentials` artifacts instead of falling into accidental non-agent or stalled remote behavior.
- A three-task Grok sample initially spent 10-13 minutes per task in OAuth because copied host auth was stale. The preflight change reduced the same stale-auth failure to a clear `harness_error` in about three seconds.
- Sample stale-auth preflight artifact: `results/runs/20260528T093026-grok-build-ethereum__deposit_contract_minimal__deposit_count`.
