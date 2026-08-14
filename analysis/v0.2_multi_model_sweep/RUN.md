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
  --benchmark-head c5a2344b121040445ccd745a3f839548ca8f9158 \
  --benchmark-manifest benchmark-versions/v0.2.json \
  --panel analysis/v0.2_multi_model_sweep/strat50/panel.json \
  --output results/strat50-p4 \
  --model zai/glm-5.2 \
  --model kimi/k3 \
  --model xai/grok-4.6 \
  --max-attempts 16 \
  --max-tool-calls 120 \
  --omit-stop-model zai/glm-5.2 \
  --omit-stop-model kimi/k3 \
  --omit-sampling-model kimi/k3
```

`--omit-stop-model` removes local-ChatML stop sentinels only for the named
compatible lane; the Grok lane retains its unmodified request shape.
`--omit-sampling-model kimi/k3` removes `temperature`, `top_p`,
and `reasoning_effort`; Kimi's coding endpoint rejects `top_p`. Both switches
are request-shape compatibility settings and do not change task content,
budgets, tools, or verifier policy.

Use the pinned `xai/grok-4.6` model identifier for reproducible comparisons;
do not publish runs made through the moving `xai/grok-4.6-latest` alias. Grok
4.6 passes the unmodified exact-shape harness preflight and therefore needs no
request-shape compatibility switch.

The runner checkpoints `results.json` after every task and resumes from existing
`SOLVED`/`GENUINE_FAIL` rows. Provider/preflight failures are classified as
infrastructure-invalid, excluded from model scores, and re-probed after a
recoverable circuit-breaker delay.

## Required preflight

Before a paid panel run, require a successful exact-shape harness preflight and
one real Lean canary for each model. A `/models` response or simple curl alone is
not sufficient.

## Muse Spark 1.2

The original 64-token protocol probe falsely rejected `muse-spark-1.2`.
Muse always reasons, and private reasoning counts against `max_tokens`; the
probe exhausted its output budget before the model could emit a tool call.
Direct Meta API tests with `reasoning_effort=minimal` produce a valid native
tool call in 85–91 completion tokens, while `medium` used about 199 tokens for
the same probe. The generic protocol-probe floor is therefore 256 tokens.

For a scored Muse run, explicitly pin and publish `reasoning_effort` rather than
using the provider-selected default. Run a same-task canary at `minimal` and
`low` first, then keep one setting for all 50 tasks. For long multi-turn agents,
Meta recommends the Responses API because Chat Completions cannot replay Muse's
private reasoning between tool turns; this benchmark currently uses Chat
Completions, so changing API protocol would be a separate harness cohort.
