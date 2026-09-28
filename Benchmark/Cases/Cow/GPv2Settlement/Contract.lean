import Contracts.Common
import Verity.Stdlib.Math

namespace Benchmark.Cases.Cow.GPv2Settlement

open Verity hiding pure bind
open Verity.EVM.Uint256
open Verity.Stdlib.Math

set_option linter.dupNamespace false

/-!
# CoW Protocol `GPv2Settlement` settle-path order ledger

Source: `cowprotocol/contracts` at `c07a93e3596194c5e3cf331c755a3f9f0e4a17d8`,
`src/contracts/GPv2Settlement.sol` (last changed in `6f1a7e9`, pragma bump) and
`src/contracts/libraries/SafeMath.sol`.

Deployed: `0x9008D19f58AAbD9eD0D60971565AA8510560ab41` (Sourcify exact match,
solc 0.7.6). After stripping comments and whitespace, the deployed sources
differ from the pinned sources only in semantics-neutral ways: the pragma, the
`modifier x {` / `x() {` form, `uint256(-1)` vs `type(uint256).max`, the loop
increment style, and a private helper's spelling in GPv2SafeERC20.

Modeled functions, with their source lines:

* `computeTradeExecution` (L337-L442): the per-trade check that `settle`
  runs for every trade through `computeTradeExecutions` (L290-L319).
* `invalidateOrder` (L250-L255).
* `freeFilledAmountStorage` (L262-L266) and one iteration of
  `freeOrderStorage` (L474-L487).
* `swapFilledAmountUpdate`: only the `filledAmount` bookkeeping of `swap`
  (L217-L230). `swap` is the fourth writer of `filledAmount`, so lifecycle
  histories must include it.

Not modeled: the rest of `swap` (L153-L216, the Balancer direct path: order
recovery, `batchSwap` limits and deadline, fee transfer) and everything
outside the functions above.

## Simplifications

1. **Bytes-keyed mapping.** Solidity's `mapping(bytes => uint256) filledAmount`
   (slot 2, keyed by the 56-byte `orderUid`) is modeled as a word-keyed
   `Uint256 → Uint256` mapping at slot 2. `verity_contract` has no bytes-keyed
   mappings (Verity gap, covered by the lfglabs-dev/verity#1724 parity
   umbrella). The proofs never rely on the key encoding: they only use that
   writes to one key leave the other keys unchanged, which holds for the real
   keccak-addressed mapping too.
2. **Field projection of memory structs.** `RecoveredOrder memory` and
   `GPv2Order.Data memory` are passed as plain parameters. This is a
   deliberate projection, not a Verity gap: struct input parameters exist at
   the pinned Verity revision. Only the fields that `computeTradeExecution`
   reads are passed: `kind`, `partiallyFillable`, `sellAmount`, `buyAmount`,
   `feeAmount`, `validTo`, and the uid. `order.kind` is a `bytes32` word
   compared against `KIND_SELL`, exactly as in Solidity: any other word takes
   the buy branch. `order.validTo` is a `uint32` in Solidity and is widened
   to `Uint256` here. For values below `2^32` the comparisons are identical,
   and larger values only add model executions. Every theorem quantifies over
   all successful executions, so admitting extra ones is a sound
   over-approximation.
3. **Transfer out-parameters.** `inTransfer`/`outTransfer` are
   `GPv2Transfer.Data memory` out-parameters. The model returns their `amount`
   fields as `(inTransfer.amount, outTransfer.amount, executedFeeAmount)`. The
   `account`, `token` and `balance` fields are copied verbatim from
   `owner`/`sellToken`/`sellTokenBalance` and
   `receiver`/`buyToken`/`buyTokenBalance`. Since no arithmetic touches them,
   they are not modeled.
4. **Events.** `Trade` and `OrderInvalidated` are omitted; they do not affect
   state.
5. **uid decoding.** `extractOrderUidParams` checks
   `orderUid.length == 56` and reads the owner and `validTo` from the uid
   bytes with assembly. The model passes owner and `validTo` as explicit
   arguments (`uidOwner`, `uidValidTo`) and omits the length check. Dropping a
   revert branch only admits extra successful model executions of
   `invalidateOrder`/`freeFilledAmountStorage`, which is a sound
   over-approximation for the lifecycle theorems. The lifecycle relation in
   `Specs.lean` ties `uidValidTo` to the order's `validTo`, as
   `packOrderUidParams` does in `recoverOrderFromTrade` for a canonical
   56-byte uid.
6. **`freeOrderStorage` loop.** The model covers one iteration, with the
   `onlyInteraction` check on the same call. Verity's `forEach` is still a
   single-body executable stub without a proof model at the pinned revision
   and upstream, so the loop is not modeled. Model assumption: a multi-uid
   call is atomic (any failing iteration reverts all of them), so its effect on
   one uid is exactly one such step.
7. **SafeMath.** `mul`, `add`, `div`, `ceilDiv` are written inline with their
   exact revert conditions. `mul` uses `safeMul`: it returns `some 0` for
   `a = 0`, matching SafeMath's early `return 0`, and reverts exactly when
   `a * b ≥ 2^256`. `add` reverts exactly on overflow. `div` and `ceilDiv`
   `require(b > 0)`. `ceilDiv` uses the source formula
   `a / b + (a % b == 0 ? 0 : 1)`, whose `+` cannot wrap because `b > 0`.
   Revert messages match the source strings.
8. **`swap` bookkeeping only.** `swapFilledAmountUpdate` reproduces
   L217-L230 of `swap`: it requires `filledAmount[uid] == 0` and an exact
   full fill, then writes `sellAmount` (sell) or `buyAmount` (buy). The Balancer
   token deltas are inputs. The Balancer Vault call, its limits, its deadline
   check and the fee transfer that precede these lines are not modeled.
   Order recovery (L158-L160) is also not modeled; the lifecycle relation
   fixes one signed order per uid.
-/

verity_contract GPv2Settlement where
  storage
    -- GPv2Signing.preSignature : mapping(bytes => uint256) := slot 0 (not modeled)
    -- ReentrancyGuard._status  : uint256                   := slot 1 (not modeled)
    filledAmount : Uint256 → Uint256 := slot 2

  constants
    -- GPv2Order.KIND_SELL = keccak256("sell")
    KIND_SELL : Uint256 :=
      0xf3b277728b3fee749481eb3e0b3b48980dbbab78658fc419025cb16eee346775

  -- GPv2Settlement.sol L337-L442, `computeTradeExecution`.
  -- Returns (inTransfer.amount, outTransfer.amount, executedFeeAmount).
  function computeTradeExecution
      (orderUid : Uint256, kind : Uint256, partiallyFillable : Bool,
       sellAmount : Uint256, buyAmount : Uint256, feeAmount : Uint256,
       validTo : Uint256, sellPrice : Uint256, buyPrice : Uint256,
       executedAmount : Uint256) : Tuple [Uint256, Uint256, Uint256] := do
    -- L349
    let now ← blockTimestamp
    require (validTo >= now) "GPv2: order expired"

    -- L368-L371: order.sellAmount.mul(sellPrice) >= order.buyAmount.mul(buyPrice)
    let limitLhs ← requireSomeUint (safeMul sellAmount sellPrice) "SafeMath: mul overflow"
    let limitRhs ← requireSomeUint (safeMul buyAmount buyPrice) "SafeMath: mul overflow"
    require (limitLhs >= limitRhs) "GPv2: limit price not respected"

    -- L373-L376
    let mut executedSellAmount := 0
    let mut executedBuyAmount := 0
    let mut executedFeeAmount := 0
    let mut currentFilledAmount := 0

    if kind == KIND_SELL then
      -- L379-L387
      if partiallyFillable then
        executedSellAmount := executedAmount
        -- order.feeAmount.mul(executedSellAmount).div(order.sellAmount)
        let feeProduct ← requireSomeUint (safeMul feeAmount executedAmount) "SafeMath: mul overflow"
        require (sellAmount > 0) "SafeMath: division by 0"
        executedFeeAmount := div feeProduct sellAmount
      else
        executedSellAmount := sellAmount
        executedFeeAmount := feeAmount

      -- L389-L391: executedSellAmount.mul(sellPrice).ceilDiv(buyPrice)
      let sellValue ← requireSomeUint (safeMul executedSellAmount sellPrice) "SafeMath: mul overflow"
      require (buyPrice > 0) "SafeMath: ceiling division by 0"
      executedBuyAmount := add (div sellValue buyPrice) (ite (mod sellValue buyPrice == 0) 0 1)

      -- L393-L399
      let filledBefore ← getMappingUint filledAmount orderUid
      let filledAfter ← requireSomeUint (safeAdd filledBefore executedSellAmount) "SafeMath: addition overflow"
      currentFilledAmount := filledAfter
      require (currentFilledAmount <= sellAmount) "GPv2: order filled"
    else
      -- L401-L409
      if partiallyFillable then
        executedBuyAmount := executedAmount
        -- order.feeAmount.mul(executedBuyAmount).div(order.buyAmount)
        let feeProduct ← requireSomeUint (safeMul feeAmount executedAmount) "SafeMath: mul overflow"
        require (buyAmount > 0) "SafeMath: division by 0"
        executedFeeAmount := div feeProduct buyAmount
      else
        executedBuyAmount := buyAmount
        executedFeeAmount := feeAmount

      -- L411: executedBuyAmount.mul(buyPrice).div(sellPrice)
      let buyValue ← requireSomeUint (safeMul executedBuyAmount buyPrice) "SafeMath: mul overflow"
      require (sellPrice > 0) "SafeMath: division by 0"
      executedSellAmount := div buyValue sellPrice

      -- L413-L417
      let filledBefore ← getMappingUint filledAmount orderUid
      let filledAfter ← requireSomeUint (safeAdd filledBefore executedBuyAmount) "SafeMath: addition overflow"
      currentFilledAmount := filledAfter
      require (currentFilledAmount <= buyAmount) "GPv2: order filled"

    -- L420: executedSellAmount = executedSellAmount.add(executedFeeAmount)
    let sellWithFee ← requireSomeUint (safeAdd executedSellAmount executedFeeAmount) "SafeMath: addition overflow"
    -- L421
    setMappingUint filledAmount orderUid currentFilledAmount
    -- L423-L441: Trade event omitted; transfer amounts returned.
    return (sellWithFee, executedBuyAmount, executedFeeAmount)

  -- GPv2Settlement.sol L250-L255, `invalidateOrder`.
  function invalidateOrder (orderUid : Uint256, uidOwner : Address) : Unit := do
    let sender ← msgSender
    require (uidOwner == sender) "GPv2: caller does not own order"
    setMappingUint filledAmount orderUid 115792089237316195423570985008687907853269984665640564039457584007913129639935

  -- GPv2Settlement.sol L262-L266 with one iteration of L474-L487.
  function freeFilledAmountStorage (orderUid : Uint256, uidValidTo : Uint256) : Unit := do
    let self ← Verity.contractAddress
    let sender ← msgSender
    require (self == sender) "GPv2: not an interaction"
    let now ← blockTimestamp
    require (uidValidTo < now) "GPv2: order still valid"
    setMappingUint filledAmount orderUid 0

  -- GPv2Settlement.sol L217-L230: the `filledAmount` bookkeeping at the end
  -- of `swap` (the Balancer direct path). Everything before it (order
  -- recovery, Balancer `batchSwap` with limits and deadline, fee transfer)
  -- is not modeled. `executedSellAmount` / `executedBuyAmount` are the token
  -- deltas that Balancer returned. The step is modeled only so that
  -- lifecycle histories can include `swap` fills. The proof makes no claim
  -- about the price `swap` executes at.
  function swapFilledAmountUpdate
      (orderUid : Uint256, kind : Uint256, sellAmount : Uint256, buyAmount : Uint256,
       executedSellAmount : Uint256, executedBuyAmount : Uint256) : Unit := do
    let filledBefore ← getMappingUint filledAmount orderUid
    require (filledBefore == 0) "GPv2: order filled"
    if kind == KIND_SELL then
      require (executedSellAmount == sellAmount) "GPv2: sell amount not respected"
      setMappingUint filledAmount orderUid sellAmount
    else
      require (executedBuyAmount == buyAmount) "GPv2: buy amount not respected"
      setMappingUint filledAmount orderUid buyAmount

end Benchmark.Cases.Cow.GPv2Settlement
