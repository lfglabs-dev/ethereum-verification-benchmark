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

- `default --mode fair` is the auditable Lean-tools mode. It exposes only generic public-file, goal, proof-check, tactic-try, and declaration-search tools, logs every tool call, and verifies the final editable file independently.
- `grok-build` is a shell-agent custom adapter over an isolated generated workspace and the same final verifier.
