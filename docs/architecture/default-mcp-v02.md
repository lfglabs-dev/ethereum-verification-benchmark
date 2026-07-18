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

## Intended file scope

* Canonical dispatch/profile and MCP identifiers: ``harness/cli.py``,
  ``harness/agents/default.json``, ``harness/runners/lean_tools_mcp.py``, and
  artifact validation.
* Obsolete runnable profile/configuration surface: the named Grok/Vibe/OpenCode
  profiles and their CLI/check/documentation references.
* Deterministic tests, including a local fake MCP transport semantic smoke.
* No files under ``benchmark-versions/``, task manifests, references, or
  committed result/leaderboard data.
