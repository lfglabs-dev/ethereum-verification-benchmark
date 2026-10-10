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

## Multi-Model Campaign Results (`p4_normal`, `reasoning_effort=low`)

Six complete 50-task cohorts and three partial/quota-blocked cohorts were evaluated on the frozen v0.3 STRAT-50 panel under `p4_normal` (`max_attempts=16`, `max_tool_calls=120`, `max_turns=50`) with `reasoning_effort="low"`. Across all evaluated models, **23 / 50 tasks (46.0%)** were solved by at least one model.

### Complete Cohorts (50/50 valid verifier verdicts, 0 `INFRA_INVALID`)

| Rank | Model | Solved | Valid Verdicts | Solve Rate | Total Tokens | Total Requests | Cum. Time (s) |
|---:|---|---:|---:|---:|---:|---:|---:|
| 1 | **`openai/gpt-6.1-sol`** | **20** | 50/50 | **40.0%** | 2,180,066 | 560 | 24,340.0 |
| 1 (tie) | **`google/gemini-4-argon-eap`** | **20** | 50/50 | **40.0%** | 2,918,787 | 480 | 16,274.9 |
| 3 | **`openai/gpt-6-luna`** | **10** | 50/50 | **20.0%** | 2,150,310 | 596 | 17,743.4 |
| 3 (tie) | **`zai/glm-5.3`** | **10** | 50/50 | **20.0%** | 3,741,342 | 702 | 16,994.3 |
| 5 | **`xai/grok-4.7`** | **8** | 50/50 | **16.0%** | 2,792,065 | 443 | 10,495.9 |
| 5 (tie) | **`anthropic/claude-opus-5-5`** | **8** | 50/50 | **16.0%** | 3,080,091 | 377 | 8,054.0 |

### Partial / Quota-Blocked Cohorts

| Model / Route | Status | Valid Verdicts | Solved | Genuine Fail | Solve Rate (Valid) | Solve Rate (/50) | Total Tokens | Notes |
|---|---|---:|---:|---:|---:|---:|---:|---|
| `muse/muse-spark-1.3` | `stopped_paid_route_disabled` | 35/50 | **8** | 27 | 22.86% | 16.00% | 3,043,546 | Paid Meta API route stopped at 35/50 per user instruction; completed verdicts preserved without relabelling. |
| `muse-code/muse-spark-1.3` | `stopped_quota_exhausted` | 1/15 | **0** | 1 | 0.00% | 0.00% | 61,777 | Muse Code subscription route for remaining 15 tasks; hit upstream subscription quota window (`resets_at: 2026-10-10T14:47:14Z`), no paid fallback. |
| `kimi/k3-256k` | `stopped_quota_exhausted` | 0/50 | **0** | 0 | 0.00% | 0.00% | 0 | Blocked by upstream Kimi 7-day weekly quota limit (`HTTP 403/429`). |

### Committed Campaign Artifacts

- [`leaderboard.json`](./leaderboard.json) — machine-readable v0.3 STRAT-50 leaderboard, solved task lists per model, and union of solved tasks (`23/50`).
- [`summary.json`](./summary.json) — per-model aggregate metrics and lane status.
- [`results.json`](./results.json) — deduplicated per-task outcomes across evaluated models.
- [`results_muse_code_subscription.json`](./results_muse_code_subscription.json) — separately labelled subscription route records for `muse-code/muse-spark-1.3`.
