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

- `default` is the auditable MCP-backed OpenAI-compatible loop and final verifier.
  It obtains its Lean inspection schemas and results from a pinned local
  `lean-lsp-mcp` stdio server. The target is `lean-lsp-mcp==0.28.0`, so it has a hard preflight on Lean
  4.24 or newer; it is not runnable on the benchmark's pre-migration Lean 4.22
  checkout.

For controlled model comparisons, run the same task panel and benchmark budget
with `default`. Compare verifier passes, reusable task count, prompt and
completion tokens, requests, tool calls, proof attempts, and wall time. Do not
merge results across differing task panels, model identifiers, temperatures,
package versions, or preflight outcomes.
