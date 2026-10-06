# KPK full-batch settlement accounting

The reference `settlement_accounting` proves the complete `SettlementAccounting`
conjunction for one actual successful `processRequests` execution over arbitrary
approved/rejected arrays, from initial `WellFormed` and `ExternalApplicability`
states and a word-range supplied price. Duplicate IDs and address aliases are
allowed. The reference needs no input-ID range premise; the unchanged generated
agent signature includes that original premise. Generated task holes remain
intentional and are excluded from default solved-reference builds.

Coverage: exact management/performance fee prefix and returned module mutation;
ordered decisions, expiry rejection and duplicate consumption; complete original
request records and terminal statuses; source-ordered nominal payments; signed
supply/share/registered-token balance vectors; finite/infinite allowance debits;
checked two-stage conversion, minimum outputs and sharp one-raw-unit floor bounds;
whole external-world replay, caller/config/request frames and selected final price.

No unfinished reference proof or custom axioms. Standard Lean axioms only:
propext, Classical.choice, Quot.sound. Independent terminal Proof+Build and Final
Red Team accepted the unchanged conjunction before promotion.

## Verify

Install the pinned Lean toolchain and dependencies, then from the repository root:

    python3 cases/kpk/shares_settlement_accounting/verify.py

Equivalent ordinary targets are:

    lake build Benchmark.Cases.KPK.SharesSettlementAccounting.Proofs
    lake build Benchmark.Cases.KPK.SharesSettlementAccounting.Compile
    lake build Benchmark.Cases.KPK.SharesSettlementAccounting.Regression

The helper creates a temporary root Lake config with per-Lean -M3000/-j1 and
170-second target timeouts, without changing dependency pins. It uses retained
caches when present; it does not bound the global Lake scheduler or aggregate
cgroup memory and does not certify a cold dependency build. Full integration was
checked separately under the same runtime-only root configuration.

## Scope

Manual source-structured logical-storage model at the pinned Verity version,
not generated Solidity/IR/Yul/EVM execution or mechanized source/bytecode refinement.
Conventional nominal registered-token behavior with coherent finite balances;
static typed token/module separation, no callbacks, tax, rebasing or reentry.
Performance module economics are excluded; exact supplied arguments, returned
issuance and module-world writes are accounted for. No fresh/fair NAV guarantee:
price is operator supplied. Economic NAV interpretation requires complete basket
value per outstanding share after fee issuance and before settlement, in the batch
asset units scaled by 1e8, and is not certified here.

Initial request sums, escrow coverage, finite support, word ranges, configured
addresses/rates/decimals and empty per-call trace are theorem premises, not a proof
of lifetime reachability or post-settlement escrow preservation. Intake,
cancellation, recovery, asset deletion, admin, upgrades and external share
transfers are outside this theorem. Applies to the retained Carry source graph,
not kUSD/kETH or all deployments; see the public `SourcePin.json` for evidence pin.
