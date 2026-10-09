# Dromos MetaDEX root allocation conservation

Selected specification from the Dromos Labs team: for every token key, the sum of chain allocations equals committed voting power, including CHAIN0 and TOKEN0.

This case proves an executable symbolic root-ledger model, not deployed Solidity or bytecode. Public source is pinned at dromos-labs/metadex-public commit 0058bd9b1d49b0fb0a6d130dd51886b2c64e3d99. Read the simplification ledger at the top of Contract.lean before interpreting the result.

## Result

`transaction_conservation` proves every Reachable state satisfies allChainInterpretation for every full-width uint256 token key. Reachable starts with initializedLedger (empty sets, zero amounts/positions/commitment) and closes under actual successful modeled entry execution. The sum is ordinary natural-number addition over any duplicate-free finite cover of all positive allocation amounts, not modular addition. The stored set supplies such a cover. Support pairing and independent positions are auxiliary proof predicates, not a second advertised property.

The executable entries are allocateChains, allocate, burn, rebalanceChain0, processDeallocation, emergencyDeallocate, parkOnChain0 and clearToken, plus a callback-inclusive nonwriter projection. Arbitrary finite loops and successful authenticated returns are covered. Concrete set insertion, removal, swap-and-pop, clear and full-width field frames are checked.

Proofs.lean, AssignmentProofs.lean and SetProofs.lean contain checked reference proofs. Dependency printing reports standard Lean foundations (propext, Classical.choice, Quot.sound) only, no case-local domain axiom or sorryAx. The generated task ends in `exact ?_` intentionally and is not the reference proof. Compile.lean elaborates the executable surface; it does not emit Yul.

## Reproduce

From the repository root, with the pinned lean-toolchain and lake-manifest.json:

```sh
LEAN_NUM_THREADS=1 timeout 170 lake build Benchmark.Cases.Dromos.AllocationConservation.Proofs
LEAN_NUM_THREADS=1 timeout 170 lake env lean -M 3000 -j1 Benchmark/Cases/Dromos/AllocationConservation/Regression.lean
python scripts/validate_manifests.py
```

Use an external aggregate-RSS guard below 2700 MiB in a 4 GiB worker; do not run heavy Lean commands concurrently. Direct case elaboration and finite regression pass under those limits. Finite tests supplement, not replace, arbitrary-input theorems.

## Applicability boundaries

The modeled authorization, sender, stake/chain/gauge-result checks, uint128 range/budget guards and transient reentry checks are runtime preconditions of successful model execution. The theorem starts from an initialized ledger; it does not repair arbitrary corrupt states. External view results are symbolic inputs.

Source correspondence is manually audited, not mechanically proved. Logical arrays and injective symbolic field channels do not prove physical nested arrays, stale backing cells, keccak layout or the OpenZeppelin transient-slot layout. Points, signed casts, slope/emission schedules, fees, event/ABI/nonce/transport handling, leaf/gauge execution and token transfers are omitted or projected. Their complete control flow and source success/failure equivalence are not verified. Transport returns are modeled as arbitrary finite authenticated deallocation sequences, not arbitrary invariant-constrained poststates. No claim covers private/deployed revisions or whole-contract safety.

Full-repository baseline and post-authoring builds were bounded/incomplete (timeout 124 or aggregate-RSS safety stop -15). They are not green; no unrelated proof defect was reached or repaired. Targeted case gates and independent scoped Build/Modelization/Verity/Proof/Red Team reviews passed.

## License

The original LICENSE and NOTICE are retained byte-for-byte. The source-derived model is modified for development, testing and formal evaluation only. See the restricted-use terms before reusing it; this is not a production implementation.
