---
name: verity-prove-invariant
description: >
  Autonomous Ralph-loop workflow for adding a new Verity benchmark case: research the
  protocol, choose and audit the invariant, model the Solidity in Verity, prove the
  invariant or produce a counterexample/explicit axiom, and write the lfglabs.dev case
  study. The parent mission is the arbitrator and replaces human gates with GPT-5.5
  high-effort reviewer missions. Trigger terms: verity prove, new benchmark case,
  prove invariant, formally verify, add verity case, verify protocol, model contract
  in verity, lean contract verification.
---

# Verity Prove Invariant

Add a new formal-verification case to the Verity benchmark. This skill is autonomous:
do not require human approval between phases. The mission that started this skill is
the **arbitrator**. It researches, implements, spawns reviewers, waits for their input,
resolves findings, and records every decision.

Human messages may redirect scope, but normal progress must not depend on a human
review gate.

---

## Sandboxed / Ralph-loop execution contract

Run this as a single `/goal` style mission. Keep state in:

```text
.context/verity-prove-invariant/<case-slug>/
├── phase-1-research.md
├── phase-2-modelization.md
├── phase-3-proof.md
├── phase-4-article.md
├── review-matrix.md
└── reviewer-reports/
```

The parent mission must:

1. Call `get_workspace_layout` once if the orchestrator tools are available.
2. Call `get_backend_auth_status` once for `codex` before spawning reviewers.
3. Spawn reviewer missions with `batch_create_workers` when two or more reviewers are
   ready.
4. Use `wait_for_any_worker` / worker status tools until every required reviewer has
   reported.
5. Continue only after critical findings are resolved or explicitly rejected with
   evidence in `review-matrix.md`.

Every spawned reviewer mission must use:

```json
{
  "backend": "codex",
  "model_override": "gpt-5.5",
  "model_effort": "high"
}
```

If the exact model is unavailable, do not silently downgrade. Record the blocker and
ask the backend/auth layer to be fixed.

---

## Reviewer report schema

Every reviewer must return exactly this structure:

```text
status: pass | pass_with_minor_findings | blocked
critical_findings:
major_findings:
minor_findings:
evidence:
required_changes:
confidence:
```

Severity rules:

- `critical_findings` block the phase.
- `major_findings` must be fixed or rejected with concrete evidence.
- `minor_findings` may be deferred if logged.
- Proof and modelization phases need at least two independent passes before the
  arbitrator can proceed.
- Axioms require approval from the Proof Reviewer and Final Red Team Reviewer.
- Counterexamples require confirmation from the Invariant Reviewer.

---

## Reviewer roles

Use these roles by default. Put the role/personality in the worker prompt.

1. **Research Reviewer**: skeptical protocol security analyst. Checks protocol facts,
   docs, source links, value at risk, and whether the selected functions matter.
2. **Invariant Reviewer**: DeFi risk and accounting specialist. Checks whether the
   invariant is meaningful, non-trivial, and neither too weak nor too broad.
3. **Modelization Reviewer**: German Solidity developer who cares deeply about
   semantics, syntax, naming, and readability. Compares Solidity to Verity
   function-by-function and flags every behavioral mismatch.
4. **Verity Reviewer**: formal-methods engineer. Checks whether claimed Verity gaps are
   real by reading `.lake/packages/verity/`, repo-local forks, docs, open issues, PRs,
   recently merged PRs, and roadmap material.
5. **Build Reviewer**: reproducibility-focused CI engineer. Runs the exact build and
   test commands and reports environment-sensitive failures.
6. **Proof Reviewer**: adversarial Lean/Verity theorem prover. Rejects `sorry`, abusive
   axioms, missing theorem coverage, and proofs that prove a weaker statement.
7. **Final Red Team Reviewer**: adversarial auditor. Tries to break the model, proof,
   assumptions, and published claim.
8. **Article Reviewer**: technical venture capitalist. Cares about concise, simple,
   clear writing that explains why the invariant matters without overclaiming.

---

## Phase 1 - Research, invariant alignment, and translation audit

Input may be a protocol name, website, Solidity address, repository, invariant idea, or
all of these. First find and read the real Solidity source.

Research:

- Protocol website and docs.
- GitHub source or verified contract source.
- Storage layout, state variables, accounting units, require checks, loops, queues,
  branch structure, external calls, and value transfers.

Write `.context/verity-prove-invariant/<case-slug>/phase-1-research.md` with:

1. One-paragraph protocol summary: what it does, who uses it, unit of value at risk,
   target contract/functions.
2. Candidate invariants, ordered from highest to lowest value. Pick the minimum
   invariant that exercises non-trivial logic.
3. Evaluation of any user-proposed invariant. Say whether it is valid, too weak, too
   strong, or mis-targeted.
4. Translation fidelity audit:
   - exact Solidity construct / snippet / path
   - closest Verity surface
   - classification: no issue / proof-gap-only / Verity-gap / hard blocker
   - syntax-only change or semantics risk
5. Draft simplifications, or `none yet`.
6. Proposed Verity issues, if any, after checking existing issues, PRs, merged PRs,
   umbrella issues, and roadmap docs.

Then spawn:

- Research Reviewer
- Invariant Reviewer

The arbitrator may continue to Phase 2 only after both reports are in and every
critical finding is resolved or rejected with evidence.

---

## Phase 2 - Modelize in Verity

Use this file layout:

```text
Benchmark/Cases/<Project>/<Case>/
├── Contract.lean
├── Specs.lean
├── Proofs.lean
└── Compile.lean

Benchmark/Generated/<Project>/<Case>/Tasks/
└── <TheoremName>.lean

cases/<project>/<case>/
├── case.yaml
├── tasks/<theorem_name>.yaml
└── verity/{Contract,Specs,Compile}.lean

families/<family>/
├── family.yaml
└── implementations/<impl>/implementation.yaml
```

The reference proof goes in `Benchmark/Cases/.../Proofs.lean`. Generated task files
stay agent-facing placeholders ending in `exact ?_`.

### Modeling rules

Model as close to Solidity as possible:

1. Preserve function boundaries, helper names, branch structure, storage layout,
   external-call boundaries, and revert conditions.
2. Prefer syntax-close rewrites that preserve semantics when exact syntax is not
   available.
3. Use narrower semantic models only as a last resort, and document each
   simplification in `Contract.lean`.

Before claiming a Verity limitation, check:

- `.lake/packages/verity/`
- any repo-local or user-provided Verity fork
- Verity docs
- Verity issues, PRs, recently merged PRs, umbrella issues, and roadmap docs

`Contract.lean` must start with a doc-comment listing every simplification and why it
was necessary. Do not call something a simplification if it can be modeled faithfully.

`Specs.lean` must define each invariant as a clear `Prop`. Use helper definitions to
hide storage-slot details and make the invariant readable.

### Build gate

Run:

```bash
lake build Benchmark.Cases.<Project>.<Case>.Contract
lake build Benchmark.Cases.<Project>.<Case>.Specs
lake build
```

Then spawn:

- Modelization Reviewer
- Verity Reviewer
- Build Reviewer

The arbitrator may continue to Phase 3 only after the modelization review passes, build
review passes, and every critical/major semantic finding is fixed or rejected with
evidence.

---

## Phase 3 - Proving persistent loop

Write `Proofs.lean` and keep looping until one terminal condition is reached.

Terminal conditions:

1. **PROOF**: `lake build Benchmark.Cases.<Project>.<Case>.Proofs` succeeds and there
   is no `sorry`.
2. **COUNTEREXAMPLE**: concrete state and inputs satisfy the hypotheses and falsify the
   conclusion. Write exact values as a comment or `#eval`.
3. **AXIOM**: an `axiom` closes the proof, with a doc-comment explaining exactly what
   is assumed, whether it holds for the real contract, and why it was not discharged
   mechanically.

Never return with "I tried X and got stuck". If `simp` leaves a residual goal, inspect
the goal and make progress. If the gap is real, add an explicit axiom with a narrow
statement and justification.

For state-transition theorems on monadic contracts, the proof usually follows:

```lean
theorem my_theorem ... := by
  unfold my_spec balanceOf supply
  by_cases hCond : <condition>
  · dsimp
    simp [ContractName.fn, getStorage, setStorage, getMapping, setMapping,
      Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure,
      Contract.run, ContractResult.snd]
  · ...
```

After reaching a terminal condition, spawn:

- Proof Reviewer
- Final Red Team Reviewer

If the terminal condition is `COUNTEREXAMPLE`, also spawn the Invariant Reviewer again.

The arbitrator may continue to Phase 4 only after:

- no `sorry` remains for a proof terminal condition
- all specs have matching proofs or documented terminal status
- every axiom is approved by Proof Reviewer and Final Red Team Reviewer
- counterexamples are confirmed by the Invariant Reviewer

Open a PR on `https://github.com/lfglabs-dev/ethereum-verification-benchmark` only after this gate
passes.

---

## Phase 4 - Article

Write a concise case study article for `https://github.com/lfglabs-dev/lfglabs.dev`.

Before writing, clone or fetch the repo and read:

- at least two existing pages in `pages/research/`
- `components/research/Guarantee.jsx`
- `components/research/Hypothesis.jsx`
- `components/research/Disclosure.jsx`
- `components/research/CodeBlock.jsx`
- `components/research/ExternalLink.jsx`
- `data/research.js`

Do not guess component APIs.

### Specs readability check

The article math must closely match `Specs.lean`. If the raw spec is hard to read,
refactor `Specs.lean` with helper definitions first, then update proofs as needed.

### Article structure

Use the existing site patterns and include:

1. The Guarantee: English and math notation matching `Specs.lean`.
2. Context: protocol, contract/function, unit of value at risk.
3. Why This Matters: concrete failure mode prevented.
4. How This Was Modeled & Proven: links, proof strategy, `lake build` command.
5. Proof Status: proven, proven with assumptions, or in progress.
6. Assumptions: every axiom and hypothesis using existing `<Hypothesis>` components.

Writing rules:

- No em dashes.
- No filler phrases.
- No inflated language.
- Short sentences.
- Active voice.
- Specific claims only.
- Do not say more was proven than the theorem coverage supports.

After drafting, spawn:

- Article Reviewer
- Final Red Team Reviewer, scoped to public claims and technical accuracy

### Final PR gate

The workflow is not complete until both PRs exist.

### Git authoring

For `verity-benchmark` and `lfglabs.dev` PRs created or updated through this skill,
commit with the user's GitHub-linked identity unless they explicitly provide a
different one:

```text
Fricoben <78437165+fricoben@users.noreply.github.com>
```

Before committing, set the repo-local Git author config or pass the author explicitly
so GitHub associates the PR commits with the `fricoben` account.

1. Open a PR on `https://github.com/lfglabs-dev/ethereum-verification-benchmark` with the complete
   benchmark case:
   - Verity model
   - specs
   - proofs or documented terminal result
   - generated task placeholders
   - case YAMLs
   - family / implementation metadata
   - reproducibility notes
2. Open a PR on `https://github.com/lfglabs-dev/lfglabs.dev` with the public case
   study:
   - research page
   - metadata entry
   - proof status
   - assumptions and hypotheses
   - guarantee matching `Specs.lean`
   - links to the benchmark PR or committed benchmark files

Only open the `lfglabs.dev` PR after the article review passes. Do not stop after local
implementation. The mission is complete only when both PR URLs are reported in the
final response.

---

## Standard reviewer worker prompt template

Use this shape for every reviewer:

```text
You are the <Role Name>.

Personality and review stance:
<role-specific personality from this skill>

Mission:
Review <phase/artifact> for <case-slug>.

Workspace:
<absolute workspace path>

Read:
- <exact files>
- .context/verity-prove-invariant/<case-slug>/<phase-file>
- any source/docs/proofs listed by the arbitrator

Do not implement broad changes unless explicitly asked. You are reviewing.

Return exactly:
status: pass | pass_with_minor_findings | blocked
critical_findings:
major_findings:
minor_findings:
evidence:
required_changes:
confidence:
```

Create this worker with:

```json
{
  "backend": "codex",
  "model_override": "gpt-5.5",
  "model_effort": "high",
  "title": "Verity <case-slug> - <review name>",
  "prompt": "<self-contained prompt>"
}
```

---

## Anti-patterns

- Waiting for a human to approve a normal phase transition.
- Continuing before reviewer missions have reported.
- Spawning reviewers without `backend: codex`, `model_override: gpt-5.5`, and
  `model_effort: high`.
- Treating a reviewer summary as enough when the cited files contradict it.
- Writing proofs in `Generated/.../Tasks/*.lean`.
- Using `sorry`.
- Hiding broad assumptions inside an axiom.
- Claiming a Verity limitation without checking the local package and upstream status.
- Modeling a high-level toy system when a closer source-structured translation is
  available.
- Publishing article math that diverges from `Specs.lean`.
- Ending Phase 4 without creating both the `verity-benchmark` PR and the `lfglabs.dev`
  PR.
- Creating Verity repository issues unless explicitly requested outside this autonomous
  workflow.
