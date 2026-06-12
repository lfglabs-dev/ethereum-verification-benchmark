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
- shell agent profiles (`grok-build`, `opencode`, `codex`, ... from `harness/agents/*.json`) are custom adapters running coding-agent CLIs over an isolated generated workspace, metered by a local proxy, with the same final verifier.
