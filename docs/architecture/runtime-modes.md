# Runtime Modes

All modes use the same task contract and evaluator.

`strict`
- no agent-visible tools
- agent returns one final proof file

`interactive`
- same contract
- adds `read_public_file`, `write_editable_proof`, `run_lean_check`, `inspect_lean_goals`, and `search_public_defs`

`custom`
- calls an external command adapter
- still uses the same file allowlist and final evaluation

Current group harnesses are concrete adapters over this task contract:

- `default` is the auditable Lean-tools harness. It exposes only generic public-file, goal, proof-check, tactic-try, and declaration-search tools, logs every tool call, and verifies the final editable file independently.
- `builtin-lean-lsp` uses the same auditable OpenAI-compatible loop and final
  verifier as `default`, but obtains its Lean inspection schemas and results from
  a pinned local `lean-lsp-mcp` stdio server. This isolates the effect of the MCP
  tool surface from the much larger architectural differences of a shell agent.
- shell agent profiles (`grok-build`, `opencode`, `codex`, ... from `harness/agents/*.json`) are custom adapters running coding-agent CLIs over an isolated generated workspace, metered by a local proxy, with the same final verifier.

For controlled model comparisons, run the same task panel and benchmark budget
with `default`, `builtin-lean-lsp`, and `vibe-lean-lsp`. The first two share the
loop, metering, and submission semantics; the last measures the complete coding
agent architecture. Compare verifier passes, reusable task count, prompt and
completion tokens, requests, tool calls, proof attempts, and wall time. Do not
merge results across differing task panels, model identifiers, temperatures,
package versions, or preflight outcomes.
