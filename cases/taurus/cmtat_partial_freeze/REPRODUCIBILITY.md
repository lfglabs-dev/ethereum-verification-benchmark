# CMTAT partial-freeze sender protection

Source: CMTAT v3.0.0, commit 69eecc9735ce8ada84fd35801888b05747658939.

- Release: https://github.com/CMTA/CMTAT/releases/tag/v3.0.0
- Enforcement: https://github.com/CMTA/CMTAT/blob/69eecc9735ce8ada84fd35801888b05747658939/contracts/modules/internal/ERC20EnforcementModuleInternal.sol
- Entry points: https://github.com/CMTA/CMTAT/blob/69eecc9735ce8ada84fd35801888b05747658939/contracts/modules/0_CMTATBaseCommon.sol
- Halborn assessment: https://github.com/CMTA/CMTAT/blob/69eecc9735ce8ada84fd35801888b05747658939/doc/audits/Halborn-CMTATv3.0.0-2025/Taurus_CMTAT_Smart_Contract_Security_Assessment_Report_Halborn.pdf

At retrieval on October 16, 2026, the upstream README and release inventory identify v3.0.0 as the latest formally audited release lineage. Halborn's July 2025 assessment and remediation/post-assessment revisions precede the final release tag. This is not a claim that every final-tag byte was independently audited. OpenZeppelin contracts-upgradeable 5.4.0 supplies the inherited token logic; dependency authorship is not a separate audit of CMTAT.

## Guarantee

In the modeled standard CMTAT variant, with RuleEngine and SnapshotEngine unset at every included call, a successful transfer or transferFrom cannot spend the sender's partially frozen amount. The amount is at most its pre-call balance minus frozen tokens; its frozen mapping is unchanged and its immediate post-call balance still covers that amount. A self-transfer is checked against the same instructed-amount limit and restores the original balance.

This covers ordinary entrypoints regardless of whether their caller also holds a privileged role. It does not cover privileged entrypoints. Repeated-call protection is per successful step against that step's prestate, not a claim of global recipient backing or preservation after arbitrary excluded operations.

## Modeling route and boundaries

Contract.lean uses source-shaped semantic functions over Verity's bounded Address and Uint256 types. It is not a verity_contract DSL compilation, Yul emitter or bytecode refinement. Solidity-to-model correspondence is reviewed by hand. Named state fields abstract ERC7201 storage namespaces; resolved caller is explicit. Events, bytes payloads and revert ABI details are omitted.

The `_update` helper represents only the nonzero-endpoint ordinary transfer branch, not mint/burn or total-supply branches. `_transfer` enforces that domain before calling it. The sender is debited before the recipient is read, preserving aliasing. Recipient credit wraps modulo 2^256 exactly as the unchecked inherited code; the model inserts no recipient overflow guard. No global supply consistency or recipient-backing theorem is asserted over arbitrary synthetic states.

RuleEngine and SnapshotEngine callbacks are absent by the selected zero-address configuration, not assumed harmless. Engine setters and upgrades are not in the ordinary trace alphabet. The standard selected variant has no ERC1363 recipient callback methods; those variants are excluded. Mint, burn, batchTransfer, crosschain operations and forcedTransfer are privileged and excluded. ForcedTransfer can deliberately unfreeze the shortfall before movement and is not covered by frozen-map immutability. Partial freeze/unfreeze helpers have separate authorization/backing facts and are not ordinary trace steps. Unfreeze preservation explicitly requires initial account backing. Forwarder authentication, authority management, enabled engines, custom subclasses, economic value and deployment identity are not established.

## Reproduce

Pinned Lean: leanprover/lean4:v4.31.0.
Pinned Verity: 85e0262baca2656ba2444ddfc2ed1d596544cd7b.
All dependencies use the repository's unchanged lake-manifest.json.

    lake build Benchmark.Cases.Taurus.CMTATPartialFreeze.Contract
    lake build Benchmark.Cases.Taurus.CMTATPartialFreeze.Specs
    lake build Benchmark.Cases.Taurus.CMTATPartialFreeze.Compile
    lake build Benchmark.Cases.Taurus.CMTATPartialFreeze.Proofs
    lake build Benchmark.Cases.Taurus.CMTATPartialFreeze.Regression
    lake env lean -M 2400 Benchmark/Cases/Taurus/CMTATPartialFreeze/Proofs.lean
    lake env lean -M 2400 Benchmark/Cases/Taurus/CMTATPartialFreeze/Regression.lean

Run these serially with resource supervision appropriate to the actual cgroup. The case-local targets and separate source elaborations pass. At the current pin, independent integration review reproduced the Proofs and Regression Lake targets, separate direct elaboration of both source files, and the Compile Lake target. Parent execution separately checked Contract, Specs and Compile through both routes. The earlier independent individual model-target review used the historical Verity pin; it is not relabeled as a current-pin execution. The whole-root baseline remains INCOMPLETE: a bounded live-main root build reached an unchanged pinned Verity/Macro/SpecGen.lean compilation and hit its wall timeout. Historical attempts under the supplied worktree's older Verity pin stopped earlier in other dependency modules. No source error was observed before termination, but that is not a completed root build or a green full suite. No source-EVM tests are claimed. The case-local success must not be generalized to repository-wide readiness.

## Proof artifacts

The original senderProtected predicate includes the amount bound, whole frozen-map equality, immediate sender backing and exact sender balance. The universal proof derives these from actual successful entrypoints, not just the partial-balance require. It checks allowance sequencing, zero-frozen branch and sequential aliasing. all_traces_protected handles both ordinary operation constructors and failed calls without imposing an initial global-backing premise.

Separate theorems cover finite/max allowances, unrelated storage frames, error rollback, successful freeze establishment and premise-qualified unfreeze preservation. The exported phase3_theorem_bundle and regression_bundle have only Lean's standard foundational dependencies (propext and, where needed, Quot.sound); no added axioms or sorry are used.

Regression.lean contains kernel-checked concrete successful and rejecting examples: the 100 balance/40 frozen boundary, self/zero transfers, finite/max transferFrom, allowance-write-before-endpoint-failure rollback, over-frozen sender rejection and separate authorized freeze/unfreeze helpers. These are semantic-model checks, not Solidity execution or an exploit demonstration.

Generated task files are agent-facing holes ending in exact ?_. Reference solutions live only in Benchmark/Cases/Taurus/CMTATPartialFreeze/Proofs.lean.
