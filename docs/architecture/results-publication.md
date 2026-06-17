# Results Publication Data Model

Benchmark consumers should not have to scan release assets or full per-task
archives to render a leaderboard. Keep three committed JSON layers:

1. `results/index.json`: small version index for website bootstrapping.
2. `results/summaries/v<version>.json`: compact public leaderboard data.
3. `results/manifests/v<version>.json`: full reusable per-model and per-task
   result index, including archive metadata and result keys.

The detailed run directories stay out of git and are published as immutable
release assets referenced by the manifest.

## Version Index

`results/index.json` is the stable entry point for websites:

```json
{
  "schema_version": 1,
  "benchmark": "verity-benchmark",
  "latest_version": "0.1",
  "versions": [
    {
      "benchmark_version": "0.1",
      "tag": "benchmark-v0.1",
      "label": "v0.1",
      "task_count": 135,
      "summary_url": "results/summaries/v0.1.json",
      "manifest_url": "results/manifests/v0.1.json"
    }
  ]
}
```

Add a new benchmark tag by appending one object and updating
`latest_version`. Existing version entries should not be mutated except for
metadata corrections.

## Summary File

`results/summaries/v<version>.json` is optimized for website rendering. It
should include one row per model run with provider and model split explicitly:

```json
{
  "schema_version": 1,
  "benchmark": "verity-benchmark",
  "benchmark_version": "0.1",
  "task_count": 135,
  "task_set_id": "sha256:...",
  "harness_id": "sha256:...",
  "environment_id": "sha256:...",
  "models": [
    {
      "provider": "openai",
      "model": "gpt-5.5",
      "model_id": "openai-gpt-55",
      "display_name": "GPT 5.5",
      "status": "complete",
      "task_count": 135,
      "valid_count": 135,
      "passed": 66,
      "failed": 69,
      "pass_rate": 0.489,
      "caveats": []
    }
  ]
}
```

The minimum fields needed by the public website are:

- `benchmark_version`
- `models[].provider`
- `models[].model`
- `models[].passed`
- `models[].failed`

`status`, `valid_count`, and `caveats` should also be exposed so the website
can distinguish complete rows from partial or invalid rows without re-parsing
the manifest.

## Full Manifest

`results/manifests/v<version>.json` remains the source of truth for reuse and
auditing. It should keep per-task rows with:

- `task_ref`
- `passed`
- `result_key`
- `task_fingerprint`
- `task_interface_id`
- `harness_status`
- `artifact_status`
- `reusable`
- `usage`
- `run_id`

Adding a model should mean adding one model object to the manifest, attaching
or updating its release archive metadata, then rerunning
`scripts/aggregate_version.py` to regenerate the summary, leaderboard, badges,
and version index.

## Aggregation Rules

- Complete rows have `valid_count == version.task_count` and no invalid
  required artifacts.
- Partial rows are visible but excluded from rank comparisons.
- Invalid zero-token or missing-verifier artifacts stay in the manifest only as
  non-reusable caveats; they must not inflate `valid_count`.
- If multiple artifacts exist for the same `(version, model_id, task_ref)`, the
  manifest should index the selected latest valid artifact and record a caveat.
- Versioned summary files are immutable after publication except for explicit
  correction commits; new models are appended to the same version summary by
  updating the manifest and regenerating derived files.
