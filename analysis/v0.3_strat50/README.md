# v0.3 STRAT-50 panel

This directory defines the reproducible 50-task evaluation panel for benchmark
v0.3.

## Frozen identity

| Field | Value |
|---|---|
| Benchmark version | `0.3` |
| Execution commit | `d46684dcaf04a8d24dabee3330df1aea517c3a54` |
| Lean | `4.31.0` |
| Full manifest | `benchmark-versions/v0.3.json` — 263 tasks |
| Task set | `sha256:ad4a77b5d7176edf532b7baab1a376df92416dee9ecd973eaffe3525bd88072b` |
| Environment | `sha256:c2b6593676b790a2ce3e0ba258b70438e286b809ff26811fe4099ff6d8dd897a` |
| Harness | `sha256:98bbe897aa65ec83d32d577a183cea1a21ba6122851048d4c591f3f55c10c729` |
| Panel | 50 tasks, seed 42, all 41 cases covered |
| Panel SHA-256 | `6921cc27d522ecbfd0798e9bca9251526f10923855cc28dde4b22507f92eaf25` |
| Recommended effort | `p4_normal`: 16 attempts, 120 tool calls |

The panel is a direct evaluation set. Its solve rate is not an unweighted
estimate of FULL-263 performance.

## Selection algorithm

`scripts/generate_stratified_panel.py` implements
`case-stratified-largest-remainder-sha256-v1`:

1. Group every v0.3 task by `case_id`.
2. Allocate one slot to every case, guaranteeing 41/41 case coverage.
3. Allocate the nine remaining slots proportionally to each case's remaining
   task count with the largest-remainder method.
4. Break allocation ties and rank tasks with SHA-256 over a versioned domain,
   seed 42, and the task reference.
5. Sort the selected task references lexicographically for stable execution order.

No runtime PRNG is used, so selection is stable across Python versions.

Regenerate it from the repository root:

```bash
python3 scripts/generate_stratified_panel.py \
  --manifest benchmark-versions/v0.3.json \
  --panel analysis/v0.3_strat50/panel.json \
  --metadata analysis/v0.3_strat50/panel-metadata.json \
  --size 50 \
  --seed 42
```

The command must reproduce the frozen panel hash above with no diff.

## Running a cohort

Create an immutable execution checkout at the manifest's declared source commit:

```bash
# Required for shallow or single-branch clones: fetch the frozen commit explicitly.
git fetch origin d46684dcaf04a8d24dabee3330df1aea517c3a54
git cat-file -e d46684dcaf04a8d24dabee3330df1aea517c3a54^{commit}
git worktree add --detach /tmp/benchmark-v0.3 \
  d46684dcaf04a8d24dabee3330df1aea517c3a54
```

Do not substitute the current `main` head: it may contain a different task set,
environment, or harness identity. The explicit fetch was verified from a fresh
`--single-branch` clone, where the commit is otherwise absent.

Run the controller from a checkout containing the v0.3 panel and current runner:

```bash
python3 scripts/run_strat50.py \
  --workdir /tmp/benchmark-v0.3 \
  --benchmark-head d46684dcaf04a8d24dabee3330df1aea517c3a54 \
  --benchmark-manifest benchmark-versions/v0.3.json \
  --panel analysis/v0.3_strat50/panel.json \
  --output results/v0.3-strat50/<cohort-id> \
  --model <exact-model-id> \
  --max-attempts 16 \
  --max-tool-calls 120
```

Provider-specific request-shape flags and protocol identity must be explicit in
the cohort provenance. Chat Completions, Responses, Anthropic Messages, and Chat
with provider reasoning-field replay are different cohorts.

## Campaign gate

Before a paid 50-task run:

1. Verify the exact provider model ID and capability response.
2. Send one minimal request in the campaign's actual request shape.
3. Run one verifier-backed Lean task canary under the intended protocol.
4. Record model, provider, protocol, request-shape policy, benchmark commit,
   task-set/environment/harness IDs, panel hash, and p4 budget.
5. Run tasks sequentially per model and serialize memory-heavy Lean verification.
6. Retry only `INFRA_INVALID`; never count infrastructure failures as model failures.
7. Publish only after 50 distinct terminal verifier verdicts belong exactly to
   this panel.

## v0.2 lifecycle

v0.2 remains immutable and reproducible at Lean 4.24. It is no longer a target
for new benchmark campaigns after the existing sweep closes.

Do not delete its manifest, panel, release artifacts, runner compatibility, or
toolchain pin: those are required to audit published v0.2 results. Product and
documentation defaults should point to v0.3; invoking v0.2 should require an
explicit version/commit selection and should never silently fall back from v0.3.
