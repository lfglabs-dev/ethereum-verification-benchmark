# v0.3 FAST-12 panel — canary

Deterministic 12-task prefix of the canonical v0.3 STRAT-50 panel for fast preflight/canary.

| Field | Value |
|---|---|
| Benchmark version | `0.3` |
| Execution commit | `d46684dcaf04a8d24dabee3330df1aea517c3a54` |
| Lean | `4.31.0` |
| Full manifest | `benchmark-versions/v0.3.json` — 263 tasks |
| Task set | `sha256:ad4a77b5d7176edf532b7baab1a376df92416dee9ecd973eaffe3525bd88072b` |
| Environment | `sha256:c2b6593676b790a2ce3e0ba258b70438e286b809ff26811fe4099ff6d8dd897a` |
| Harness | `sha256:98bbe897aa65ec83d32d577a183cea1a21ba6122851048d4c591f3f55c10c729` |
| Panel | 12 tasks — prefix (lexicographic) of STRAT-50, `sha256:9d0e598eef246aad4717015489568a53f983333eef05b69c05c357de017b867d` |
| Source panel | STRAT-50 `sha256:6921cc27d522ecbfd0798e9bca9251526f10923855cc28dde4b22507f92eaf25` |
| Cases covered | 9/41 (canary — not stratified) |
| Recommended effort | `p4_normal`: 16 attempts, 120 tool calls |

This panel is **not independently stratified** — it cannot cover all 41 cases with 12 slots.
It is the first 12 refs of `analysis/v0.3_strat50/panel.json` (lexicographic order, stable).
It is strictly a subset of STRAT-50 and of the 100-task extended panel below.
Use it only as a fast canary before a full STRAT-50 or extended run.

```
python3 scripts/run_strat50.py \
  --workdir /tmp/benchmark-v0.3 \
  --benchmark-head d46684dcaf04a8d24dabee3330df1aea517c3a54 \
  --benchmark-manifest benchmark-versions/v0.3.json \
  --panel analysis/v0.3_fast12/panel.json \
  --output results/v0.3-fast12/<cohort-id> \
  --model xai/grok-4.6 \
  --max-attempts 16 \
  --max-tool-calls 120
```

