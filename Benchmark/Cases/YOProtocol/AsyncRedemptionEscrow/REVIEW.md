# Review matrix

This file records the independent review gates for the YO Protocol async-redemption
escrow benchmark. Reviewer runs used Codex with `gpt-5.6-terra` and `xhigh`
reasoning. Transient reviewer logs and prompts remain outside the committed benchmark.

| Phase | Review | Status | Finding | Resolution |
| --- | --- | --- | --- | --- |
| Research | Protocol source and deployment provenance | Pass with minor findings | Authorization ordering, privileged `manage`, upgrade scope, and snapshot-specific Redeemer permissions needed explicit treatment. | The model preserves the nonzero authority call before owner comparison. `manage`, later upgrades, and snapshot configuration are excluded from the theorem scope. |
| Research | Invariant selection | Pass with minor findings | The original claim needed queue aggregation, malformed-pair, fee, rollback, replay, and wrapper companion coverage. | The suite was expanded to 14 theorem interfaces, including source-reachable one-sided records and non-proportional settlements. |
| Modelization | Solidity and inherited OpenZeppelin fidelity | Pass after remediation | Earlier drafts simplified transfer ordering, success observations, and external-call boundaries too broadly. | The final model restores zero-address and pause ordering, observes `ContractResult.success`, and exposes authority, preview, balance-read, and token outcomes explicitly. |
| Modelization | Verity semantics | Pass with one deferred minor finding | Event logs are omitted. | The omission is documented. Events do not affect the selected storage and accounting properties. |
| Modelization | Reproducible build | Pass | None after remediation. | Targeted modules, the full Lake build, manifest validation, reference audit, and 14-task mapping passed. |
| Proof | Initial adversarial proof review | Remediated | Case and task manifests still reported `not_started`; Phase 2 prose was stale. | All YO manifests now report `complete`, metadata was regenerated, and the prose was corrected. |
| Proof | Initial red-team review | Pass after remediation | The same stale proof-status metadata was the only remaining finding. | Metadata was regenerated from the corrected manifests. Forced Proofs and Compile builds, 20 witnesses, theorem-header parity, and axiom inspection passed. |
| Proof | Final post-metadata rereview | Pass with minor findings | Two generated task headers used unqualified `MAX_UINT256`; after remediation, `Proofs.lean` still emits non-blocking style-linter warnings and a global `--rehash` build encounters an unrelated stale ProofWidgets cache. | Both task headers use `Verity.Stdlib.Math.MAX_UINT256`. Lean accepted all 14 task interfaces directly from their reference theorems. Forced direct Proofs and Compile checks, manifest validation, reference audit, metadata equality, proof-hygiene checks, and dependency inspection passed. No release change is required. |

## Scope decisions

- The proof establishes per-receiver aggregate accounting, bounds, and selected
  isolation properties. It does not establish per-request provenance or economic
  proportionality.
- Successful authority, oracle preview, external balance reads, and token transfers
  are explicit trusted boundary outcomes. No callback may mutate modeled vault
  storage during those boundaries.
- The pinned underlying token is distinct from the vault where address aliasing
  affects the claim.
- Events, unrelated ERC-4626 deposit and mint paths, privileged `manage` transitions,
  future upgrades, oracle correctness, and external token storage are outside scope.
- The theorem suite intentionally captures source-permitted zero-component and
  non-proportional settlements, dormant one-sided records, later repair by a queued
  request, full-clear replay behavior, fee changes, authorization fallback, and
  rollback at reached failure boundaries.

## Release gate

The final proof rereviewer confirmed exact 14 of 14 generated-task/reference type
parity, clean proof hygiene, passing manifest and reference audits, metadata equality,
and fresh direct Proofs and Compile checks. The case is cleared for release.
