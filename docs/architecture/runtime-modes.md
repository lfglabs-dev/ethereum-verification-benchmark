# Runtime Modes

All modes use the same task contract and evaluator.

The canonical runtime is:

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
