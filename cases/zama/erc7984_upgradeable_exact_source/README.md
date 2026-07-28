# Zama ERC7984Upgradeable exact-source transfer case

This case is tied to the exact Zama `protocol-apps` source at commit
`2f88eef1d0b545438b1f74e21cdff7ea771805da`:

- source: `contracts/confidential-wrapper/contracts/token/ERC7984Upgradeable.sol`
- retained copy: `upstream/ERC7984Upgradeable.sol`
- Git blob: `c24aea5237bf34db183ec0c72c4180f96a1777ea`
- SHA-256: `c504d7a7000e7bc188b5ae35d3fbe3f80ceddd219e87c8d049d66f3a11273b74`

`upstream/source-metadata.md` records the reproduction commands. The retained
Solidity is provenance evidence. `Benchmark/Cases/Zama/ERC7984UpgradeableExactSource/Contract.lean`
is a separate, transfer-focused semantic model; it is not presented as an
automatic or line-by-line translation of all Solidity behavior.

## What is modeled

The Lean model preserves the selected base `ERC7984Upgradeable` transfer path:

1. successful public input-proof/ACL wrapper validation as an explicit trusted
   Boolean precondition;
2. `_transfer` nonzero sender and receiver checks;
3. `_update` reading the sender balance handle;
4. `require(FHE.isInitialized(fromBalance), ERC7984ZeroBalance(from))` before
   `tryDecrease` and before any storage write;
5. the `tryDecrease`/`FHE.select` behavior in which an initialized insufficient
   balance yields a successful transferred amount of zero;
6. source and destination plaintext-equivalent balance updates, with explicit
   modulo-2^64 destination arithmetic.

Initialization is represented by a logical mapping separate from the modeled
plaintext-equivalent encrypted balance. The storage fields are logical; the
model does not claim physical ERC-7201 slot equivalence.

## Proved reference theorems

`Proofs.lean` contains four proofs with no `sorry` or added axioms:

- `uninitialized_sender_reverts_without_writes`: after wrapper and plaintext
  address guards pass, an uninitialized sender returns the modeled
  `ERC7984ZeroBalance` revert with the exact original `ContractState`. The
  theorem has no positive-amount hypothesis, so it includes amount zero.
- `initialized_transfer_no_balance_revert`: after the same guards and sender
  initialization, balance sufficiency selects the transferred amount but does
  not select success versus revert.
- `initialized_insufficient_transfer_zero`: for distinct parties and a
  uint64-range recipient balance, insufficiency returns zero and preserves both
  plaintext-equivalent balances.
- `initialized_transfer_pair_conservation`: for distinct parties and a
  destination addition that cannot wrap for the amount actually selected,
  sender-plus-recipient plaintext-equivalent accounting is conserved.

The generated benchmark task modules intentionally contain `exact ?_`
placeholders. They are evaluation interfaces; the complete reference solutions
remain in `Proofs.lean`.

## Explicitly not proved

The theorems do not cover FHE cryptographic correctness or ACL side effects,
public input-proof verification itself, transfer-and-call callbacks/refunds,
`ConfidentialWrapper` denylist or staticcall gates, wrap/unwrap rate conversion,
underlying ERC-20 transfer behavior or collateralization, gateway/signature
behavior, events, upgrade authorization, all other inherited functions, or
physical ERC-7201 storage slot derivation. An earlier wrapper failure can revert
before `ERC7984ZeroBalance`; the exact-revert theorem explicitly assumes the
modeled wrapper and plaintext address checks pass.

## Relationship to the retained OpenZeppelin reference

This case does not replace or mutate `zama/erc7984_confidential_token`. That
separate benchmark retains OpenZeppelin Confidential Contracts commit
`83364738f0d2b1655c60627588e3493099c359f7`. Its selected source lacks the
pre-write initialization guard present in this pinned Zama file, so results from
the two cases must be reported separately.
