# Run STRAT-50

Prepare a separate immutable v0.2 execution checkout:

```bash
git worktree add --detach /tmp/benchmark-v0.2 \
  c5a2344b121040445ccd745a3f839548ca8f9158
```

The recommended comparison is **STRAT-50 at `p4_normal`**:

- 50 identical tasks per model;
- 16 proof attempts maximum;
- 120 tool calls maximum;
- one sequential task stream per model;
- different providers may run in parallel;
- Lean verification remains bounded by `DEFAULT_HARNESS_VERIFY_CONCURRENCY=1`.

Run the controller from the results branch while pointing it at that immutable
checkout. The controller fails closed if the execution HEAD differs:

```bash
python3 scripts/run_strat50.py \
  --workdir /tmp/benchmark-v0.2 \
  --panel analysis/v0.2_multi_model_sweep/strat50/panel.json \
  --output results/strat50-p4 \
  --model zai/glm-5.2 \
  --model kimi/k3 \
  --max-attempts 16 \
  --max-tool-calls 120 \
  --omit-stop \
  --omit-sampling-model kimi/k3
```

`--omit-stop` removes local-ChatML stop sentinels rejected by ZAI, Muse, and
Kimi endpoints. `--omit-sampling-model kimi/k3` removes `temperature`, `top_p`,
and `reasoning_effort`; Kimi's coding endpoint rejects `top_p`. Both switches
are request-shape compatibility settings and do not change task content,
budgets, tools, or verifier policy.

The runner checkpoints `results.json` after every task and resumes from existing
`SOLVED`/`GENUINE_FAIL` rows. Provider/preflight failures are classified as
infrastructure-invalid, excluded from model scores, and re-probed after a
recoverable circuit-breaker delay.

## Required preflight

Before a paid panel run, require a successful exact-shape harness preflight and
one real Lean canary for each model. A `/models` response or simple curl alone is
not sufficient.

## Muse Spark 1.2

Direct Meta API and sandboxed.sh probes produce the same result for
`muse-spark-1.2`: HTTP transport and usage accounting work, but native-tool and
JSON-fallback probes return `content: null`, no `tool_calls`, and consume the
completion budget as reasoning until `finish_reason: length`. This is an
endpoint/model protocol incompatibility, not evidence that sandboxed.sh drops a
valid tool call. Do not score Muse until an endpoint or model configuration
passes the exact harness preflight.
