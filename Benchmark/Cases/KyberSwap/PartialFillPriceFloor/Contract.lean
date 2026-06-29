import Contracts.Common
import Verity.Stdlib.Math

namespace Benchmark.Cases.KyberSwap.PartialFillPriceFloor

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

/-
  Verity model of KyberSwap MetaAggregationRouterV2._checkReturnAmount.

  Source: verified Ethereum contract
  0x6131b5fae19ea4f9d964eac0408e4408b66337b5, MetaAggregationRouterV2.sol.

  In scope:
  - the `_PARTIAL_FILL` flag check
  - the partial-fill require:
      `returnAmount * desc.amount >= desc.minReturnAmount * spentAmount`
  - the non-partial require:
      `returnAmount >= desc.minReturnAmount`
  - Solidity 0.8 checked multiplication semantics for the two partial-fill
    products, modeled with `mulPanic`

  Simplifications:
  - `SwapDescriptionV2` is projected to the three fields used by this helper:
    `amount`, `minReturnAmount`, and `flags`.
  - Public entrypoints, executor calls, token transfers, fee receivers, refunds,
    calldata, permits, and events are out of scope. This benchmark proves the
    helper-level guard over values already computed by the public path.

  Economic-reading boundary:
  - Read as an effective-price floor, the partial-fill guard
    (`returnAmount * amount >= minReturnAmount * spentAmount`) is a floor only
    when `spentAmount <= amount`, i.e. the executor spends no more than the user
    quoted. The helper does not enforce this and the theorem does not assume it;
    the proof covers the inequality exactly as written.
-/

/-- `_PARTIAL_FILL = 0x01` in MetaAggregationRouterV2. This is the only flag
    `_checkReturnAmount` reads. The other router flags (`_REQUIRES_EXTRA_ETH`,
    `_SHOULD_CLAIM`, `_SIMPLE_SWAP`, ...) are not exercised by this helper and
    are omitted. -/
def partialFillFlag : Uint256 := 1

structure SwapDescriptionV2 where
  amount : Uint256
  minReturnAmount : Uint256
  flags : Uint256
deriving Repr

def _flagsChecked (flags flag : Uint256) : Bool :=
  and flags flag != 0

def isPartialFill (desc : SwapDescriptionV2) : Bool :=
  _flagsChecked desc.flags partialFillFlag

def checkedScaledPriceFloorHolds
    (spentAmount returnAmount : Uint256)
    (desc : SwapDescriptionV2) : Prop :=
  match safeMul returnAmount desc.amount, safeMul desc.minReturnAmount spentAmount with
  | some left, some right => left >= right
  | _, _ => False

verity_contract MetaAggregationRouterV2 where
  storage

  function _checkReturnAmount
      (spentAmount : Uint256, returnAmount : Uint256, amount : Uint256,
       minReturnAmount : Uint256, flags : Uint256) : Unit := do
    -- _flagsChecked(desc.flags, _PARTIAL_FILL): desc.flags & 0x01 != 0
    if and flags 1 != 0 then
      -- Solidity 0.8 checked products (revert on overflow):
      -- returnAmount * desc.amount and desc.minReturnAmount * spentAmount.
      let left ← mulPanic returnAmount amount
      let right ← mulPanic minReturnAmount spentAmount
      require (left >= right) "Return amount is not enough"
    else
      require (returnAmount >= minReturnAmount) "Return amount is not enough"
    return ()

end Benchmark.Cases.KyberSwap.PartialFillPriceFloor
