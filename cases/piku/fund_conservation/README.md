# piku/fund_conservation

Source:
- `InverterNetwork/contracts`
- commit `8b7bc438344d646bab05b751c8eb4a7f0c8ca588`
- files:
  - `src/modules/fundingManager/oracle/FM_PC_Oracle_Redeeming_v1.sol`
  - `src/modules/paymentProcessor/PP_Queue_v1.sol`
  - `src/modules/paymentProcessor/PP_Queue_ManualExecution_v1.sol`

Focus:
- `_sellOrder`
- `amountPaid`
- queued redemption accounting
- ghost-ledger fund conservation

Invariant:
- `distributedBacking + _openRedemptionAmount + remainingBacking + protocolTreasuryFees + projectTreasuryFees = initialBacking`

Out of scope:
- deployed-storage-only conservation
- oracle price calculation and decimal conversion
- queue linked-list shape
- failed or unclaimable payment branch
- payment order array lifecycle and `_outstandingTokenAmounts` accounting
- ERC20 transfer mechanics, allowance, and blacklist fallback
- access control and receiver validation

Notes:
- `initialBacking`, `distributedBacking`, `remainingBacking`, `protocolTreasuryFees`, and `projectTreasuryFees` are ghost accounting slots.
- `amountPaid` models successful direct queue settlement. Protocol fee recalculation is abstracted as an explicit `protocolCollateralFeeAmount`; this case does not prove equivalence to `PP_Queue_v1._calculateProtocolFeeAmount`.
- `remainingBacking` is a ghost solvency precondition, not a Solidity storage slot or source-level revert.
