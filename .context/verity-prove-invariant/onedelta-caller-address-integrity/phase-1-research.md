# Phase 1 - Research and Invariant Alignment

## Protocol summary

1delta is a DeFi transaction composer for spot, margin, lending, transfer, permit, flash-loan, and swap-callback operations packed into compact calldata batches. The target is the verified Ethereum `OneDeltaComposerEthereum` deployment at `0x97648606fcc22bd96f87345ac83bd6cFCdF0ACBa`, deployed at block `23665178` on `2025-10-27T00:21:47`. The accepted scope is `contracts/1delta/composer/chains/ethereum/Composer.sol` plus `contracts/1delta/composer/BaseComposer.sol`, with the fund-pull paths in `AssetTransfers.sol`, `V3Callbacker.sol`, and callback routing in the Ethereum flash-loan and flash-swap callback contracts. The value at risk is user ERC20 and Permit2 allowance granted to the composer or Permit2 path by the original `deltaCompose` caller, not protocol TVL. Codeslaw reports low verified-deployment activity as of the captured page: 165 inbound calls and 0 outbound calls over the last year.

## Candidate invariants

1. Caller-address integrity for fund pulls. Every modeled ERC20 `transferFrom` and Permit2 `transferFrom` that pulls user funds during one `deltaCompose` batch uses the outermost `deltaCompose` caller as `from`, including transfer-command pulls and the direct Uniswap V3-style swap callback shortcut.
2. Callback caller preservation. Any callback re-entry that continues the packed operation dispatcher must forward the same caller identity received from the authenticated callback payload.
3. Command-offset monotonicity. The dispatcher must advance offsets correctly for the modeled transfer commands.

The selected invariant is 1. It is the minimum property that directly protects user allowances and exercises the non-trivial caller propagation through `deltaCompose`, command dispatch, and nested callbacks. It is not a generic accounting invariant.

## Evaluation of user-proposed invariant

The proposed invariant is valid and well-targeted. The relevant source has an explicit `callerAddress` parameter whose documentation says it is the address that initially triggered `deltaCompose` and is called within flash and swap callbacks. The important security question is whether all fund-pull call sites consume that propagated identity rather than `msg.sender`, `address(this)`, an intermediate pool/callback contract, or unrelated embedded calldata address bytes. The invariant is narrow enough to model with transfer commands, Permit2 transfer commands, flash callback propagation, swap callback propagation, and the V3 callback direct ERC20 pull.

## Translation fidelity audit

| Solidity construct | Source path | Verity surface | Classification | Risk |
| --- | --- | --- | --- | --- |
| `deltaCompose(bytes)` passes `msg.sender` to `_deltaComposeInternal` | `BaseComposer.sol` | `deltaCompose` reads `msgSender` and stores `outerCallerWord`; decoded dispatcher paths are exposed as path-specific entrypoints | no issue | syntax-only calldata abstraction |
| `_deltaComposeInternal(address callerAddress, ...)` dispatches `_transfers(..., callerAddress)` and flash/singleton paths with the same caller | `BaseComposer.sol` | `_deltaComposeInternal_*`, callback, and V3 direct-pull entrypoints all receive `callerAddress` explicitly | no issue | command ids decoded rather than byte offsets |
| `TransferIds.TRANSFER_FROM = 0`, `PERMIT2_TRANSFER_FROM = 4` | `DeltaEnums.sol` | `TRANSFER_FROM` and `PERMIT2_TRANSFER_FROM` constants | no issue | none |
| `_transfers` routes transfer ids to `_transferFrom` and `_permit2TransferFrom` with the same `callerAddress` | `Transfers.sol` | `_transfers_transferFrom` and `_transfers_permit2TransferFrom` path entrypoints | no issue | unsupported branches represented by invalid-operation stubs |
| `_transferFrom` writes `callerAddress` as ERC20 `transferFrom` first argument | `AssetTransfers.sol` | ERC20 occurrence flag plus `erc20TransferFromWord` event-log slot | proof-gap-only | external call modeled as recorded call arguments |
| `_permit2TransferFrom` writes `callerAddress` as Permit2 `from` argument | `AssetTransfers.sol` | Permit2 occurrence flag plus `permit2TransferFromWord` event-log slot | proof-gap-only | external call modeled as recorded call arguments |
| `clSwapCallback` with `calldataLength == 0` writes `callerAddress` as ERC20 `transferFrom` first argument | `V3Callbacker.sol` | V3 occurrence flag plus `v3CallbackTransferFromWord` event-log slot | proof-gap-only | external pool call modeled as recorded call arguments |
| Flash-loan callbacks override `_deltaComposeInternal` and concrete callbacks forward decoded caller data | `FlashLoanCallbacks.sol` and callback implementations | `flashLoanCallbackTransferFrom` records and forwards `callerAddress` | proof-gap-only | callback authentication not modeled |
| Swap callbacks override `_deltaComposeInternal` and fallback selects concrete callback handlers | `SwapCallbacks.sol` and callback implementations | `swapCallbackPermit2TransferFrom` and `v3SwapCallbackDirectTransferFrom` record and forward `callerAddress` | proof-gap-only | DEX selector validation not modeled |

## Callback-source audit

| Callback class | Source evidence | Caller propagation result |
| --- | --- | --- |
| Aave V2 | `AaveV2Callback.sol` validates `initiator == address(this)`, decodes `origCaller` from params, then calls `_deltaComposeInternal(origCaller, ...)`. | Preserves decoded outer caller after flash-loan validation. |
| Aave V3 | `AaveV3Callback.sol` validates `initiator == address(this)`, decodes `origCaller`, then calls `_deltaComposeInternal(origCaller, ...)`. | Preserves decoded outer caller after flash-loan validation. |
| Balancer V2 flash loan | `BalancerV2Callback.sol` decodes `origCaller` from params and calls `_deltaComposeInternal(origCaller, ...)`. | Preserves decoded outer caller. |
| Morpho flash loan | `MorphoCallback.sol` decodes `origCaller` from callback calldata and calls `_deltaComposeInternal(origCaller, ...)`. | Preserves decoded outer caller. |
| Moolah flash loan | `MoolahCallback.sol` decodes `origCaller` from callback calldata and calls `_deltaComposeInternal(origCaller, ...)`. | Preserves decoded outer caller. |
| Uni V2 swap callback | `UniV2Callback.sol` validates callback sender context, decodes `callerAddress`, and calls `_deltaComposeInternal(callerAddress, ...)`. | Preserves decoded outer caller. |
| Uni V3 swap callback | `UniV3Callback.sol` decodes `callerAddress` and passes it to `clSwapCallback`; `V3Callbacker.sol` either uses it directly in ERC20 `transferFrom` when `calldataLength == 0` or forwards it to `_deltaComposeInternal`. | Preserves decoded outer caller and has a direct ERC20 pull path now modeled. |
| Uni V4 swap callback | `UniV4Callback.sol` decodes `callerAddress` and calls `_deltaComposeInternal(callerAddress, ...)`. | Preserves decoded outer caller. |
| Dodo V2 swap callback | `DodoV2Callback.sol` validates callback sender context, decodes `callerAddress`, and calls `_deltaComposeInternal(callerAddress, ...)`. | Preserves decoded outer caller. |
| Balancer V3 unlock callback | `BalancerV3Callback.sol` decodes `callerAddress` and calls `_deltaComposeInternal(callerAddress, ...)`. | Preserves decoded outer caller. |

## Draft simplifications

- Packed calldata parsing is represented by decoded command ids. This preserves the caller-address semantics because the modeled transfer operations do not read the source address from calldata.
- External ERC20 and Permit2 calls are modeled by storage event-log slots that record the `from` argument. This is the standard narrow boundary needed for the invariant.
- Token, receiver, amount, balance fallback, approvals, lending, non-transfer swaps, and accounting are out of scope.
- Callback authentication is treated as a precondition of the callback layer. The benchmark proves identity preservation after the callback path has obtained the intended outer caller. It does not claim to prove DEX or flash-loan callback authenticity.
- The full verified source snapshot is pinned locally under `cases/onedelta/caller_address_integrity/upstream/full-source/` so callback details can be audited against the same Codeslaw source tree.
- Broader swapper and lending `transferFrom` paths in the full composer are intentionally outside this benchmark. This case proves the transfer-command pulls plus the V3 callback direct-pull shortcut accepted for this scoped model.

## Sources

- Verified source and deployment metadata: `https://www.codeslaw.app/contracts/ethereum/0x97648606fcc22bd96f87345ac83bd6cfcdf0acba`
- 1delta operation docs: `https://docs.1delta.io/api/operations.html`
- 1delta transfers docs: `https://docs.1delta.io/api/transfers`

## Proposed Verity issues

None yet. The current model uses existing Verity surfaces: `msgSender`, storage slots, address-to-word conversion, conditional dispatch, and ordinary monadic functions. No upstream Verity limitation is required for this phase.

## Tooling note

The skill asks for orchestrator backend/auth calls and batch worker tools. Those tools are not available in this Codex session. Reviewer missions will be spawned with the available Codex `spawn_agent` API using `model: gpt-5.5` and `reasoning_effort: high`, matching the requested backend/model/effort as closely as the active tool surface permits.
