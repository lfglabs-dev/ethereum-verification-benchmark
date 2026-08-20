# v0.3 Extended-100 panel

Reproducible 100-task evaluation panel for benchmark v0.3 — same algorithm as STRAT-50, larger budget.

| Field | Value |
|---|---|
| Benchmark version | `0.3` |
| Execution commit | `d46684dcaf04a8d24dabee3330df1aea517c3a54` |
| Lean | `4.31.0` |
| Full manifest | `benchmark-versions/v0.3.json` — 263 tasks |
| Task set | `sha256:ad4a77b5d7176edf532b7baab1a376df92416dee9ecd973eaffe3525bd88072b` |
| Environment | `sha256:c2b6593676b790a2ce3e0ba258b70438e286b809ff26811fe4099ff6d8dd897a` |
| Harness | `sha256:98bbe897aa65ec83d32d577a183cea1a21ba6122851048d4c591f3f55c10c729` |
| Panel | 100 tasks, seed 42, all 41 cases covered |
| Panel SHA-256 | `sha256:8c0244ec4c7a028baf2db300d7058a71a38de86f03440c050aa492fc8c05362f` |
| Recommended effort | `p4_normal`: 16 attempts, 120 tool calls |

Selection: `case-stratified-largest-remainder-sha256-v1` — same as STRAT-50.
Guarantees 41/41 case coverage, remaining 59 slots proportional to remaining task count.
Strict superset of STRAT-50 (intersection = 50).

Regenerate:

```bash
python3 scripts/generate_stratified_panel.py \
  --manifest benchmark-versions/v0.3.json \
  --panel analysis/v0.3_extended100/panel.json \
  --metadata analysis/v0.3_extended100/panel-metadata.json \
  --size 100 \
  --seed 42
```

Campaign gate and execution checkout identical to STRAT-50 (see `analysis/v0.3_strat50/README.md`).

