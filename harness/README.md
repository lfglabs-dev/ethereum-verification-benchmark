# Harness

The benchmark has two kinds of harness, both running in isolated generated
workspaces and verified by the same independent verifier:

- `default`: the built-in fair Lean-tools harness (OpenAI-compatible tool loop).
- `builtin-lean-lsp`: the same built-in fair loop, budgets, metering, and
  verifier, with its Lean IDE surface supplied by a pinned `lean-lsp-mcp`
  subprocess.
- shell agent profiles from `harness/agents/*.json` (`grok-build`, `opencode`, `codex`, ...): off-the-shelf coding-agent CLIs metered through a local proxy.

Task contract:
- fixed implementation files
- fixed specification files
- one editable proof file per target
- one theorem name per target

Main entrypoints:
- `python3 -m harness.cli list --suite active --unit group`
- `python3 -m harness.cli run-task <project/case/task> --harness default`
- `python3 -m harness.cli run-group <project/case> --harness default`
- `python3 -m harness.cli run-group <project/case> --harness builtin-lean-lsp`
- `python3 -m harness.cli run-suite --suite active --harness default`
- `python3 -m harness.cli run-group <project/case> --harness grok-build` (any profile id works)
- `python3 -m harness.cli compare --runs results/runs/*`
- `scripts/run_default_harness_group.sh <project/case>`
- `scripts/run_default_harness_suite.sh --suite active`

Core files:
- `harness/manifests.py`: group/task manifest loader and scoring metadata
- `harness/workspace_builder.py`: generated group workspaces and file manifests
- `harness/verifier.py`: independent policy and Lean verifier
- `harness/cli.py`: group list/run-task/run-group/run-suite/compare CLI
- `harness/runners/lean_tools.py`: default fair harness (tool loop + run orchestration)
- `harness/runners/lean_tools_mcp.py` + `harness/lean_lsp_mcp_client.py`:
  builtin fair-loop entrypoint and pinned MCP stdio bridge
- `harness/transport.py`, `harness/lean_check.py`, `harness/proof_patch.py`, `harness/symbols.py`: chat transport, Lean checking/diagnostics, proof patching, public-symbol parsing
- `harness/runners/shell_agent.py` + `harness/agents/*.json`: shell coding-agent adapter and profiles

The default harness is agent-first: no hardcoded proof candidates and no
theorem/task-name dispatch. The model works through Lean-native tools
(`show_task`, `read_file`, `show_goal`, `definition_outline`, `tactic_sandbox`,
`check_proof`, `try_tactics`, `search_declarations`); endpoints that return
JSON-encoded tool calls as assistant text are accepted as a compatibility
path. Assistant messages land in `conversations/*.jsonl`, tool calls in
`tool-calls/*.jsonl`, checked candidates in `attempts/*.lean`, all summarized
in `harness-response.json`. Missing remote API credentials produce a
`missing_credentials` artifact instead of accidentally comparing against a
non-agent path.

`builtin-lean-lsp` is the controlled middle point between `default` and
`vibe-lean-lsp`: it retains the default harness's chat loop, provider preflight,
completion-token accounting, attempt/tool budgets, artifact format, editable-file
guards, and independent verifier, but replaces the bespoke Lean inspection tools
with the native schemas and implementations returned by `lean-lsp-mcp`.
Model-visible MCP tools are `lean_goal`, `lean_term_goal`,
`lean_diagnostic_messages`, `lean_code_actions`, `lean_hover_info`,
`lean_completions`, `lean_file_outline`, `lean_declaration_file`,
`lean_references`, `lean_local_search`, and `lean_multi_attempt`. The benchmark
keeps `show_task`, `read_file`, and `check_proof` for briefing, public source
access, and metered final submissions. Network search, arbitrary Lean snippets,
builds, widgets, profiling, and verifier-like MCP tools are disabled. Every MCP
file argument is checked against the isolated public workspace before dispatch.

The builtin profile pins `lean-lsp-mcp==0.27.0`. Version 0.28.0 exposes the same
selected surface but its client requires Lean 4.24 or newer, while this benchmark
pins Lean 4.22. Comparisons must record the resolved package version from
`run.json`/`harness-response.json`.

Task briefing:
- Every task/group workspace contains `harness/TASK_SUMMARY.md`.
- The summary is shared by fair default and Grok Build and includes target theorem names, editable files, implementation/specification files, the exact `./harness/check.sh` command, policy, and current editable theorem skeletons.
- Grok Build appends the initial check result to the summary before the shell agent starts. The fair default agent receives the same summary through `show_task`.
- `definition_outline`, `search_declarations`, and `read_file` can inspect public Lean dependency files under `.lake` and the generic Grindset modules; hidden proof files and `.env` are absent and blocked.
- Fair task results include `failure_class`, distinguishing provider/context failures, no-tool loops, context loops, proof parse errors, unknown names, unsolved goals, Lean timeouts, and other Lean failures.

Budget profiles:
- `quick`: `max_attempts=4`, `max_tool_calls=40`, `max_turns=20`, `shell_timeout_seconds=900`.
- `normal`: `max_attempts=16`, `max_tool_calls=120`, `max_turns=50`, `shell_timeout_seconds=2400`.
- `deep`: `max_attempts=48`, `max_tool_calls=400`, `max_turns=100`, `shell_timeout_seconds=7200`.
- Explicit `--max-attempts`, `--max-tool-calls`, `--max-turns`, or `--shell-timeout-seconds` override the selected profile.

Default harness API env:
- `DEFAULT_HARNESS_BASE_URL`
- `DEFAULT_HARNESS_MODEL`
- `DEFAULT_HARNESS_DRIVER_MODEL`: optional orchestration-loop model override
  (defaults to `DEFAULT_HARNESS_MODEL`)
- `DEFAULT_HARNESS_PROVER_MODEL`: optional model used only by the hybrid
  proof-drafting tool
- `DEFAULT_HARNESS_PROVER_MODE=draft_proof`: exposes the hybrid `draft_proof`
  tool to the driver when `DEFAULT_HARNESS_PROVER_MODEL` is also set
- `DEFAULT_HARNESS_PROVER_BASE_URL`: optional separate OpenAI-compatible endpoint
  for the hybrid prover. When unset the prover reuses `DEFAULT_HARNESS_BASE_URL`
  (single-endpoint hybrid). Set it to run a cross-provider hybrid where the
  driver/tool loop and the prover live on different providers.
- `DEFAULT_HARNESS_PROVER_API_KEY`: optional API key for
  `DEFAULT_HARNESS_PROVER_BASE_URL`. When unset the prover reuses the driver key
  (`DEFAULT_HARNESS_API_KEY`) only if it targets the driver endpoint; on a
  separate prover host no Authorization header is sent, so the driver credential
  is never shared with another provider.
- `DEFAULT_HARNESS_API_KEY`
- `DEFAULT_HARNESS_REQUEST_TIMEOUT_SECONDS`
- `DEFAULT_HARNESS_STREAMING` (`1` default; set `0` to disable SSE streaming)
- `DEFAULT_HARNESS_STREAM_IDLE_TIMEOUT_SECONDS` controls the allowed idle gap
  between SSE chunks when streaming is enabled
- `DEFAULT_HARNESS_REQUEST_RETRIES`
- `DEFAULT_HARNESS_REQUEST_RETRY_BACKOFF_SECONDS`
- `DEFAULT_HARNESS_MAX_TOOL_CALLS`
- `DEFAULT_HARNESS_MAX_RESPONSE_TOKENS`
- `DEFAULT_HARNESS_NATIVE_TOOLS`
- `DEFAULT_HARNESS_TOOL_RESULT_CHARS`
- `DEFAULT_HARNESS_TASK_SUMMARY_CHARS`
- `DEFAULT_HARNESS_MAX_NON_PROOF_TOOL_CALLS`
- `DEFAULT_HARNESS_LEAN_MCP_STARTUP_TIMEOUT_SECONDS` (default 180)
- `DEFAULT_HARNESS_LEAN_MCP_TOOL_TIMEOUT_SECONDS` (default 600)
- `DEFAULT_HARNESS_CONTEXT_TOKENS` if the provider supports an `n_ctx` request hint
- `DEFAULT_HARNESS_TOKEN_BUDGET` to stop a task after N completion tokens (0 = unlimited);
  per-task and aggregate `usage` is reported in `harness-response.json` and `run.json`
- `DEFAULT_HARNESS_WARM_BUILD_TIMEOUT_SECONDS` for the one-time dependency warm build
  the fair runner performs per target module before the agent loop starts (default 1800)
- `DEFAULT_HARNESS_HTTP_USER_AGENT` to override the request User-Agent (default
  `ethereum-verification-benchmark-harness/1.0`; some proxies reject the Python default UA)
- `DEFAULT_HARNESS_CHECK_MODE`: `file` (default) checks the editable proof file with
  `lake env lean` (seconds; falls back to `lake build` on dependency-graph errors),
  `module` always runs the full `lake build <target>`
- `DEFAULT_HARNESS_STUCK_NUDGE`: `1` (default) appends a change-strategy nudge when a
  proof attempt repeats the same error signature; failed attempts also carry a
  failure-class `hint` (unsolved goals, unknown name, parse, type, timeout)

Fair-mode behavior notes:
- Before any agent request, the runner builds each target module once so agent-visible
  Lean check timeouts measure proof elaboration rather than cold dependency builds.
  Run `lake exe cache get && lake build` on the host before benchmarking.
- `check_proof`/`try_tactics` accept either a tactic body (placed under `:= by` with
  relative indentation preserved verbatim) or a complete Lean file with imports,
  helper lemmas, and the target theorem. Submissions that change the target theorem
  statement are rejected with `statement_mismatch` feedback.
- `show_goal` does not consume the non-proof tool budget.
- Hybrid draft-proof mode keeps the driver responsible for all tool orchestration,
  Lean diagnostics, and proof submission. When `DEFAULT_HARNESS_PROVER_MODE` is
  `draft_proof`, the driver also sees `draft_proof {task_context, goal, errors}`.
  That tool calls `DEFAULT_HARNESS_PROVER_MODEL` with a strict proof-body-only
  prompt and returns an unchecked candidate. Rejected prover output containing
  markdown, JSON, theorem statements, `sorry`, `admit`, `axiom`, or placeholders
  is reported as a tool result and is not counted as a proof attempt. Only
  `check_proof`/`try_tactics` submissions count as proof attempts. Draft audit
  logs are written under `results/runs/<run_id>/draft-proofs/`.
- The prover can run on a separate provider from the driver. Set
  `DEFAULT_HARNESS_PROVER_BASE_URL` (and optionally `DEFAULT_HARNESS_PROVER_API_KEY`)
  to route only the `draft_proof` prover calls to that endpoint; the driver/tool
  loop keeps using `DEFAULT_HARNESS_BASE_URL`/`DEFAULT_HARNESS_API_KEY`. When these
  prover values are unset the prover reuses the driver endpoint, so existing
  single-endpoint hybrid runs are unaffected. The resolved `prover_base_url` is
  recorded in the run manifest (`harness-response.json`) and in each draft audit
  log entry; API keys are never logged.

Local runtime configuration:
- Copy `.env.example` to `.env`.
- Put local provider keys and model settings in `.env`.
- `.env` is ignored by git and loaded by `harness.cli` before runner startup.
- Existing process environment variables take precedence over values in `.env`.
- To switch between configured providers without editing the generic endpoint,
  set `DEFAULT_HARNESS_PROVIDER=qwen` or `DEFAULT_HARNESS_PROVIDER=glm`.
  The selected profile reads `DEFAULT_HARNESS_QWEN_*` or
  `DEFAULT_HARNESS_GLM_*` values first, then falls back to the generic
  `DEFAULT_HARNESS_*` values.

Compatibility env still accepted by the default harness:
- `GAZELLA_BASE_URL`
- `GAZELLA_MODEL`
- `GAZELLA_API_KEY`
- `OPENAI_API_KEY`

Grok auth:
- CI/local automation should set `GROK_CODE_XAI_API_KEY`.
- Host `~/.grok/auth.json` is not copied unless `VERITY_ALLOW_HOST_GROK_AUTH=1`.
- Without usable auth, the Grok runner writes a `harness_error` artifact instead of blocking on an interactive login prompt. It preflights `grok models` inside the isolated run home so stale copied host auth fails quickly.

Useful commands:

```bash
python3 -m harness.cli list --suite active --unit group
python3 -m harness.cli run-task ethereum/deposit_contract_minimal/deposit_count --harness default --max-attempts 2 --keep-workspace
python3 -m harness.cli run-task ethereum/deposit_contract_minimal/deposit_count --harness builtin-lean-lsp --max-attempts 2 --max-tool-calls 24 --keep-workspace
# Provider-free MCP smoke: performs initialize, tools/list, and a real lean_local_search call.
python3 scripts/smoke_builtin_lean_lsp_mcp.py
DEFAULT_HARNESS_DRIVER_MODEL=minimax/minimax-m3 DEFAULT_HARNESS_PROVER_MODEL=mistralai/Leanstral-2603 DEFAULT_HARNESS_PROVER_MODE=draft_proof python3 -m harness.cli run-task ethereum/deposit_contract_minimal/deposit_count --harness default --max-attempts 2 --max-tool-calls 12 --keep-workspace
# Cross-provider hybrid: MiniMax driver controls tools on the default endpoint,
# Leanstral prover drafts proof bodies on a separate provider endpoint.
# Set DEFAULT_HARNESS_BASE_URL / DEFAULT_HARNESS_API_KEY for the MiniMax driver and
# DEFAULT_HARNESS_PROVER_BASE_URL / DEFAULT_HARNESS_PROVER_API_KEY for Leanstral.
DEFAULT_HARNESS_DRIVER_MODEL=minimax/minimax-m3 DEFAULT_HARNESS_PROVER_MODEL=mistralai/Leanstral-2603 DEFAULT_HARNESS_PROVER_MODE=draft_proof DEFAULT_HARNESS_PROVER_BASE_URL=https://leanstral-provider.example/v1 python3 -m harness.cli run-task ethereum/deposit_contract_minimal/deposit_count --harness default --max-attempts 2 --max-tool-calls 12 --keep-workspace
python3 -m harness.cli run-task ethereum/deposit_contract_minimal/deposit_count --harness default --budget deep
python3 -m harness.cli run-group ethereum/deposit_contract_minimal --harness default --max-attempts 2 --keep-workspace
python3 -m harness.cli run-suite --suite active --harness default --max-attempts 1
VERITY_ALLOW_HOST_GROK_AUTH=1 python3 -m harness.cli run-task ethereum/deposit_contract_minimal/deposit_count --harness grok-build --max-turns 20
VERITY_ALLOW_HOST_GROK_AUTH=1 python3 -m harness.cli run-task ethereum/deposit_contract_minimal/deposit_count --harness grok-build --budget deep
python3 -m harness.cli run-group ethereum/deposit_contract_minimal --harness grok-build --dry-run --max-turns 20 --keep-workspace
python3 -m harness.cli run-suite --suite active --harness grok-build --dry-run
python3 -m harness.cli compare --runs results/runs/<default-fair-run> results/runs/<grok-build-run>
python3 scripts/check_run_artifacts.py results/runs/<run_id>
python3 scripts/check_group_workspaces.py ethereum/deposit_contract_minimal
```
