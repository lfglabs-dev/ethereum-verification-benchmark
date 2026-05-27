# Next PR: Fair Lean Agent Harness

## Objective

Turn the `default` harness into an agent-first Lean proof harness that is specialized for proof work without encoding benchmark-specific answers.

The harness should behave more like `grok-build` in that an agent inspects the task workspace, chooses actions, edits proofs, and iterates from verifier feedback. Its specialization should come from Lean-native tools, not from hardcoded task candidates.

## Non-Goals

- Do not optimize headline pass rate with case-specific proof bodies.
- Do not dispatch on benchmark family, case, task, or theorem names.
- Do not add grindset lemmas that are effectively reference solutions for one task.
- Do not replace `grok-build`; keep it as the general shell-agent baseline.

## Architecture

Add a fair mode for the default harness:

```text
workspace_builder
  -> default Lean agent runner
      -> inspect task metadata and editable files
      -> call Lean-native tools
      -> propose proof edits
      -> check attempts with Lean
      -> iterate from diagnostics
  -> independent verifier
```

The agent should drive the loop. The harness provides tools and enforces policy.

## Modes

Add explicit modes to `default`:

```bash
--mode fair
--mode tuned
--mode legacy
```

- `fair`: default comparison mode. Agent-first, no case-specific candidates, no theorem-name dispatch, no answer-like helper imports.
- `tuned`: allows documented reusable helper libraries, but still no task-name answer dispatch.
- `legacy`: preserves the current hardcoded local candidates for regression/debugging only.

## Lean Tools

Implement a small tool layer that the agent can call:

- `show_task`: return task manifest, target theorem, editable files, and allowed modules.
- `read_file`: read allowed workspace files.
- `show_goal`: insert a proof prefix and return Lean goal state or diagnostics.
- `check_proof`: patch a proposed proof body and run the task target.
- `try_tactics`: try generic tactic snippets such as `simp`, `simp_all`, `aesop`, `omega`, `linarith`, `nlinarith`, `constructor`, `rcases`, `by_cases`, `split`, `ext`, and `funext`.
- `search_declarations`: search imported public declarations by symbol/name/text.

Tools should return compact, structured output. Every tool call and attempted proof should be logged in run artifacts.

## Fairness Policy

In `fair` mode:

- Reject code paths that branch on group, case, task, or theorem names.
- Disable current local proof candidates.
- Forbid imports from answer-like grindset modules.
- Allow only public task files, generic libraries, and generated harness files in the workspace.
- Record success source as one of:
  - `agent_direct`
  - `agent_with_lean_tools`
  - `agent_with_search`
  - `failed`

## Implementation Steps

1. Add `--mode fair|tuned|legacy` to `harness.cli` and the default runner config.
2. Move existing local candidate generation behind `legacy`.
3. Rename or wrap `harness/runners/lean_tools.py` as the default Lean runner entry point.
4. Add `harness/lean_agent/` with session, tools, prompts, patching, and policy modules.
5. Implement the first agent loop using the existing OpenAI-compatible API settings.
6. Add artifact logs for tool calls, proof attempts, Lean diagnostics, and success source.
7. Add checks that `fair` mode does not call legacy candidate dispatch or import task-specific helper modules.
8. Compare `default --mode fair`, `default --mode legacy`, and `grok-build` on a small fixed suite.

## Definition of Done

- `python3 -m harness.cli run-task <task> --harness default --mode fair` works end to end.
- Fair mode performs at least one model-driven Lean tool loop before submitting.
- Legacy candidates are unavailable unless `--mode legacy` is passed.
- Run artifacts include tool-call and proof-attempt traces.
- CI checks pass.
- README documents the three modes and the fair comparison command.
