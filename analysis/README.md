# Task taxonomy & model failure clustering

This directory holds the **annotation and analysis layer** for the Ethereum verification benchmark:
what kind of proof problem each task is, what proof skills it exercises, and how models
fail on it. It answers the questions in
[issue #93](https://github.com/lfglabs-dev/ethereum-verification-benchmark/issues/93) — *which tasks are
hard, which are divisive, and why* — without changing how the benchmark scores anything.

Keep this directory for curated, reproducible analysis inputs and summaries. Raw
experiment logs, PID files, and in-progress cascade outputs belong under ignored
`output/` paths locally, then either get promoted into a small curated analysis
artifact or attached as release assets.

## Why this is a separate layer

Scoring (pass/fail, tokens, `result_key`, rerun planning) lives in
`benchmark-versions/`, `results/manifests/`, and `scripts/plan_rerun.py`. That layer is
governed by fingerprints: change a task and its result is invalidated and rerun.

The taxonomy here is the opposite kind of artifact. It is **hand-maintainable, keyed by
`task_ref`, and decoupled from versioning**:

- It is **never an input to `result_key`** and **never triggers a rerun**. You can add a
  skill tag, rename a failure mode, or relabel a task without invalidating a single stored
  result. (Enforced by `tests/test_task_taxonomy.py::DecouplingInvariantTests`.)
- Each reviewed label records the **`task_fingerprint` it was reviewed against**, so drift
  is detectable: if a task's current fingerprint no longer matches its label's fingerprint,
  the label is flagged for re-review — but result reuse is unaffected.

This is the acceptance requirement that the taxonomy be *updatable without invalidating
results or requiring reruns*.

## Files

| File | Hand-authored? | What it is |
| --- | --- | --- |
| `failure_modes.json` | yes | The failure-mode taxonomy: outcome statuses (level 1) + Lean failure sub-modes (level 2). Data-driven source of truth consumed by `scripts/classify_failures.py`; extend it without code changes. |
| `task_taxonomy.json` | yes | Schema + `skill_vocabulary` + reviewer-curated seed labels (skills, observed failure modes, cohort signatures) for an initial set of tasks. |
| `task_features.json` | generated | Per-task aggregate + per-model detail (pass/fail, tokens, parsed failure mode) over a benchmark version. Produced by `extract_task_features.py`. |
| `model_task_matrix.csv` | generated | Models × tasks pass/fail matrix — a spreadsheet-friendly view of the same data. |
| `reports/hard_tasks.md` | generated | Human-readable report: hardest tasks, divisive tasks, pass rate by family/difficulty, failure modes by family. Produced by `cluster_task_failures.py`. |

The three generated files are committed for convenience (they are reproducible from public
release artifacts, see below). **Do not hand-edit them** — regenerate instead.

## The two-level failure taxonomy

`failure_modes.json` classifies every proof attempt on two levels:

1. **Outcome status** (from the verifier/harness): `passed`, `lean_check_failed`,
   `theorem_missing`, `timeout`, `dependency_checkout_failed`, `harness_error`,
   `no_submission`.
2. **Lean failure sub-mode** (parsed from the verifier output, only when
   `lean_check_failed`): `sorry_used`, `syntax_error`, `unknown_identifier`,
   `type_mismatch`, `recursion_depth`, `heartbeat_timeout`, `decision_procedure_failed`,
   `simp_no_progress`, `tactic_failed`, `unsolved_goals`, `other_lean_error` (fallback).

Sub-modes are matched **in array order, first match wins** — more specific / more proximate
causes precede the soft terminal state `unsolved_goals`. Some modes capture a detail (the
offending tactic name, the decision procedure, the unknown identifier) via named-group
regexes. `classify_failures.py` is a thin deterministic interpreter over this file; adding a
signature never requires touching code.

> Note: `heartbeat_timeout` (per-declaration elaboration budget; reported by the verifier as
> `lean_check_failed`) is deliberately distinct from the outcome-level `timeout` (the
> verifier's wall-clock budget). Don't collapse them.

## Skill vocabulary

`task_taxonomy.json` carries a controlled `skill_vocabulary` so labels stay comparable
across reviewers. Each label tags the **reasoning a passing proof requires**, independent of
any model's outcome (e.g. `state_threading`, `aggregation_conservation`,
`access_control_reasoning`, `refinement_alignment`, `revert_reasoning`). `observed_failure_modes`
on a label is the *derived* counterpart — a snapshot of how models actually failed.

## Regenerating the analysis

`task_features.json` / `model_task_matrix.csv` / `hard_tasks.md` derive from two committed
inputs (the version manifest and the results manifest) plus, optionally, **detailed run
artifacts** for failure-mode enrichment. The detailed artifacts are public GitHub release
assets, so the whole pipeline is reproducible by anyone:

```bash
# 1. (optional, for failure-mode enrichment) pull detailed run artifacts.
#    These are release assets on tag v0.1. NOTE: the manifest's asset_url uses the
#    tag `benchmark-v0.1`, which 404s; download from tag `v0.1` explicitly.
mkdir -p /tmp/v93_artifacts && cd /tmp/v93_artifacts
gh release download v0.1 --repo lfglabs-dev/ethereum-verification-benchmark   # then extract the tarballs

# 2. extract per-task / per-model features (+ enrichment if --runs-dir is given).
python3 scripts/extract_task_features.py \
  --runs-dir /tmp/v93_artifacts/runs \
  --runs-dir /tmp/v93_artifacts/minimax/runs \
  --runs-dir /tmp/v93_artifacts/kimi/runs

# 3. render the hard/divisive-task report.
python3 scripts/cluster_task_failures.py
```

Without `--runs-dir`, step 2 still produces the full pass/fail/token matrix; only the parsed
Lean failure-mode columns are omitted (`enrichment_present: false`).

## Comparison cohort

Cross-model statements (pass rate, divisiveness, P/F signatures) use a **comparison
cohort**: models that attempted at least `--min-coverage` (default `1.0`, i.e. every task) of
the version. This is the apples-to-apples set — no model is scored on a task it never
attempted, and there is no cherry-picking of which models to include. For v0.1, use the
complete rows in `results/leaderboards/v0.1.json`.

`divisiveness = 1 - |2·cohort_pass_rate − 1|` (0 = unanimous, 1 = evenly split). Note that a
very weak full-coverage model can drag a task toward "unanimous fail"; the transparent
per-task P/F **signature clusters** in the report are the more honest model-differentiation
view.

## Data-quality findings

The pipeline surfaced issues worth tracking, not silently smoothing over:

- **`difficulty: "low"` outlier.** One v0.1 task
  (`ipor/plasma_vault_redeem_split/fee_payout_bounded_by_fee_free`) carries the label `low`
  instead of the expected `easy | medium | hard`. The taxonomy notes this; treat as `easy`
  until the version metadata is corrected.
- **Mislabeled a-priori difficulty.** Some `easy`-labeled tasks are unsolved by the entire
  cohort and expensive (e.g. `usual/dao_collateral/swap_conservation`, ~650k mean tokens).
  The report's "pass rate by author-assigned difficulty" section is the empirical check on
  the a-priori labels.
