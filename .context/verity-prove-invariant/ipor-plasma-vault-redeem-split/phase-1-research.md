IPOR Fusion PlasmaVault is an ERC4626-style vault system. This case targets the
public fee-charging redeem arithmetic path in `PlasmaVault.sol`, specifically
conversion with virtual offsets, withdraw-fee shares, burning requested shares,
and transferring assets for post-fee shares.

Candidate invariants:
1. PPS non-decrease after successful public redeem. Selected. This is the
   safety property that remains true after the failed split-payout target.
2. Fee-charging payout is bounded by fee-free payout. Selected as a sanity
   theorem.
3. Split payout is bounded by combined payout plus one rounding unit. Rejected.
   The retained-fee state update makes it too strong.

Translation fidelity audit:
- `DECIMALS_OFFSET = 2`: modeled as `virtualShares = 100`.
- `_convertToAssets`: modeled as floor division by `shares + m`, with
  numerator `amountShares * (assets + 1)`.
- public `redeem`: modeled as the fee-charging path only.
- `_redeem`: modeled as burning all requested shares while paying only net
  shares after fee.
- markets, release queues, access control, external transfers, and request
  redemption are outside this arithmetic slice.

Reviewer outcome:
Research and invariant reviewers agreed the pivot to PPS non-decrease is honest.
They blocked on stale metadata and the old split-bound task. Those items were
removed or updated.
