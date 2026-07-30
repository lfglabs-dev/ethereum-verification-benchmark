# Default MCP Architecture (v0.2)

## Before this change

``default`` selected the bespoke ``lean_tools`` dispatch.  The separately named
``builtin-lean-lsp`` profile selected the same runner with ``lean-lsp-mcp``
enabled.  Grok Build, Vibe, and OpenCode profiles remained runnable through the
generic shell-agent dispatch.  Frozen v0.2 contract/environment validation ran
before any of these dispatches.

## After this change

``default`` is the sole runnable benchmark harness and always dispatches to the
MCP-backed Lean implementation.  The MCP client is responsible for declaration
lookup, diagnostics/goals, and structured tool-result resumption; it retains
the existing fail-closed classifier, role configuration, and recorded model
provenance.  The named native Grok/Vibe/OpenCode profiles are not part of the
runnable canonical architecture.  Historical result rows and frozen v0.2
task/source/reference/environment fingerprints are data, not migration input,
and remain unchanged.

## Artifact lifecycle

Canonical MCP artifacts record `mcp_lifecycle`. A run that ends before launch
uses `{"status":"not_attempted","reason":...}` with exactly one of
`dry_run`, `missing_credentials`, `dependency_warm_failed`, or
`target_warm_failed`. All other runs must record an attempted/finished MCP
lifecycle together with session metadata and MCP preflight. `impossible` and
`fallback` are explicit non-canonical states: the artifact validator rejects
them, fallback backends, and unproven pre-launch claims.

New default artifacts also record `schema_version: 2` and
`execution_contract: "default-mcp-v1"`. The validator recognizes historical
bespoke default artifacts only when their complete recorded v1 identity is
`track: "group/lean_tools"` plus `tool_backend: "builtin"`; it does not infer
legacy status from `harness_id` alone. A current schema/contract, incomplete
identity, or contradictory identity is therefore validated as MCP (and fails
closed without the MCP lifecycle evidence).

## Intended file scope

* Canonical dispatch/profile and MCP identifiers: ``harness/cli.py``,
  ``harness/agents/default.json``, ``harness/runners/lean_tools_mcp.py``, and
  artifact validation.
* Obsolete runnable profile/configuration surface: the named Grok/Vibe/OpenCode
  profiles and their CLI/check/documentation references.
* Deterministic tests, including a local fake MCP transport semantic smoke.
* No files under ``benchmark-versions/``, task manifests, references, or
  committed result/leaderboard data.
