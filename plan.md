# PR Plan: Benchmark Versioning + Rerun Planner

## Objective

Make benchmark results explicitly tied to a benchmark version, and make it possible to update model results incrementally when a new benchmark version changes only a small part of the task set.

Version `0.1` is the baseline. Future versions such as `0.2` should be able to reuse valid `0.1` task results whenever the task, harness, and environment fingerprints prove that reuse is valid.

## Non-Goals

- Do not implement advanced task taxonomy or clustering in this PR.
- Do not change benchmark tasks except where needed to compute stable metadata and fingerprints.
- Do not change model scoring semantics.
- Do not force detailed per-task run artifacts into git history.
- Do not make partially completed model columns look like complete benchmark results.

## Design

Introduce explicit version manifests and per-result validity keys.

```text
benchmark-versions/v0.1.json
  -> benchmark version metadata
  -> ordered task refs
  -> task_set_id
  -> harness_id
  -> environment_id

results/manifests/v0.1.json
  -> model result summaries
  -> release asset references for detailed archives
  -> archive sha256 checksums
  -> per-task result fingerprints

scripts/compute_fingerprints.py
  -> task fingerprints
  -> harness fingerprint
  -> environment fingerprint

scripts/plan_rerun.py
  -> compares benchmark versions
  -> decides which tasks must be rerun for a model

scripts/aggregate_version.py
  -> rebuilds leaderboard/results/badges for a version
```

## Fingerprints

Use separate fingerprints so compatibility decisions are explainable.

- `task_set_id`: ordered list of included task refs.
- `task_fingerprint`: files and task metadata that affect one task's expected proof target.
- `task_interface_id`: public files, editable files, theorem name, allowed modules, and task manifest fields visible to the model.
- `harness_id`: harness code, prompt/policy files, runner mode, budget, verifier integration, and tool surface.
- `environment_id`: Lean toolchain, Lake manifests, dependency lockfiles, and verifier/runtime dependencies.
- `result_key`: model id plus benchmark version, task ref, task fingerprint, task interface id, harness id, environment id, mode, effort/budget, temperature policy, and endpoint/provider caveats.

## Version Manifest

Add `benchmark-versions/v0.1.json` generated from the current inventory and committed as the baseline.

Required fields:

```json
{
  "benchmark": "verity-benchmark",
  "benchmark_version": "0.1",
  "created_at": "2026-06-16",
  "git_sha": "...",
  "manifest_schema_version": 1,
  "task_count": 135,
  "task_set_id": "sha256:...",
  "harness_id": "sha256:...",
  "environment_id": "sha256:...",
  "mode": "fair",
  "budget": "normal",
  "tasks": []
}
```

Each task entry should include at least:

- `task_ref`
- `family_id`
- `case_id`
- `task_id`
- `task_fingerprint`
- `task_interface_id`
- existing inventory metadata such as `proof_family`, `property_class`, and `difficulty` when available.

## Rerun Planner

Add `scripts/plan_rerun.py`.

Expected usage:

```bash
python3 scripts/plan_rerun.py \
  --from benchmark-versions/v0.1.json \
  --to benchmark-versions/v0.2.json \
  --model openai-gpt-55 \
  --results-manifest results/manifests/v0.1.json
```

Planner behavior:

- If `harness_id` changes, mark all tasks as requiring rerun.
- If `environment_id` changes, mark all tasks as requiring rerun unless an explicit `--allow-env-compatible` flag is passed.
- If a task is added, mark only that task as requiring run.
- If a task is removed, exclude it from the new aggregate.
- If a task's `task_fingerprint` changes, mark that task as requiring rerun.
- If only non-execution metadata changes, reuse the previous result.
- If a model's previous result has zero usage, missing verifier output, or an error-only artifact, do not reuse it.
- Emit both machine-readable JSON and a concise human-readable summary.

## Result Manifests

Add `results/manifests/v0.1.json` as the committed index for detailed artifacts.

It should reference GitHub Release assets instead of committing `results/runs/` directly.

Each model entry should include:

- model id and display name
- benchmark version
- result status: `complete`, `partial`, or `invalid`
- task count, valid count, pass/fail counts
- token totals
- caveats such as forced temperature, rate pacing, endpoint/provider routing, or partial-credit stop reason
- archive asset name, release tag, asset URL, byte size, and SHA-256
- per-task result entries with result keys and artifact ids.

## Aggregation

Add or update aggregation so version-specific summaries are reproducible.

Targets:

- `results/summaries/v0.1.json`
- `leaderboard.md`
- `results.json`
- `badges/*.json`

Rules:

- Complete rows are eligible for the main leaderboard.
- Partial rows must be labeled partial and excluded from complete-rank comparisons unless explicitly requested.
- Caveats must be preserved next to affected rows.
- Aggregation should be deterministic from `benchmark-versions/<version>.json` plus `results/manifests/<version>.json`.

## Implementation Steps

1. Add `scripts/compute_fingerprints.py`.
2. Generate and commit `benchmark-versions/v0.1.json`.
3. Add `results/manifests/v0.1.json` pointing at the existing `v0.1` release assets.
4. Add `scripts/plan_rerun.py` with JSON and text output.
5. Add `scripts/aggregate_version.py` or adapt the existing summary code to consume version/result manifests.
6. Update README/docs with the versioning model and standard commands.
7. Add focused tests for fingerprint stability, changed-task detection, harness-change invalidation, and partial-result rejection.

## Test Plan

- Generate `v0.1` twice and verify identical fingerprints with no source changes.
- Copy `v0.1` to a synthetic `v0.2`, change one task file, and verify only that task is planned for rerun.
- Change a harness prompt/policy file in a synthetic fixture and verify all tasks are planned for rerun.
- Change only descriptive metadata and verify existing task results are reused.
- Confirm zero-token/error-only artifacts are rejected by the planner.
- Rebuild summaries for `v0.1` from manifests and compare them with the current leaderboard data.

## Definition of Done

- `benchmark-versions/v0.1.json` exists and identifies the current 135-task benchmark.
- `results/manifests/v0.1.json` indexes the GitHub Release artifacts for version `0.1`.
- `scripts/plan_rerun.py` can explain exactly which tasks need rerun between two benchmark versions.
- Version-specific aggregation can regenerate leaderboard, JSON results, and badges.
- Documentation explains how to create `0.2`, plan reruns, run only changed tasks, and publish updated artifacts.
- Tests cover the core compatibility rules.
