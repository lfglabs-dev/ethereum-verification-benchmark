import Verity.Specs.Common
import Benchmark.Cases.Cow.GPv2Settlement.Contract

namespace Benchmark.Cases.Cow.GPv2Settlement

open Verity
open Verity.EVM.Uint256

/-!
# Specifications: CoW GPv2Settlement settle path never violates a limit order

Notation used below, for one signed order:

* `S` = `sellAmount`, `B` = `buyAmount`, `F` = `feeAmount` (signed fields).
* A successful modeled call returns nominal amounts: `sold = inAmount - fee`
  (sell-token amount excluding the fee), `bought = outAmount` (buy-token
  amount) and `fee`, where `inTransfer.amount = sold + fee` and
  `outTransfer.amount = bought`. Token movements, payer/receiver identity and
  delivery are not modeled.
* The *limit amount* is `S` for sell orders and `B` for buy orders. The
  *filled part* of a trade is `sold` for sell orders and `bought` for buy
  orders. `filledAmount[orderUid]` accumulates it.

All quantities are compared as natural numbers (`Uint256.val`), so no wrap
can hide inside a spec.
-/

/-- The fields of a signed order that `computeTradeExecution` reads. The
order uid is a hash of all of them, so they are fixed for a given uid. -/
structure SignedOrder where
  kind : Uint256
  partiallyFillable : Bool
  sellAmount : Uint256
  buyAmount : Uint256
  feeAmount : Uint256
  validTo : Uint256

/-- `order.kind == GPv2Order.KIND_SELL`. Any other kind word is treated as a
buy order, exactly as in the Solidity `else` branch. -/
def isSellOrder (o : SignedOrder) : Prop :=
  o.kind = GPv2Settlement.KIND_SELL

instance (o : SignedOrder) : Decidable (isSellOrder o) := by
  unfold isSellOrder; infer_instance

/-- `S` for sell orders, `B` for buy orders: the amount `filledAmount` may reach. -/
def limitAmount (o : SignedOrder) : Nat :=
  if isSellOrder o then o.sellAmount.val else o.buyAmount.val

/-- The part of an execution that counts towards `filledAmount`. -/
def filledPart (o : SignedOrder) (sold bought : Nat) : Nat :=
  if isSellOrder o then sold else bought

/-- The order owner never gets a worse rate than signed:
`bought / sold ≥ B / S`, written without division as
`bought * S ≥ sold * B`. -/
def respectsLimitPrice (o : SignedOrder) (sold bought : Nat) : Prop :=
  sold * o.buyAmount.val ≤ bought * o.sellAmount.val

/-- The fee is at most `F` pro rata to the filled fraction:
`fee / F ≤ filled / limitAmount`, written without division. -/
def feeWithinSignedFee (o : SignedOrder) (fee filled : Nat) : Prop :=
  fee * limitAmount o ≤ o.feeAmount.val * filled

/-- `filledAmount[orderUid]` in a contract state. -/
def filledOf (s : ContractState) (orderUid : Uint256) : Nat :=
  (s.storageMapUint GPv2Settlement.filledAmount.slot orderUid).val

/-- The modeled `computeTradeExecution` call for a fixed signed order. The
solver chooses `sellPrice`, `buyPrice` and `executedAmount`. -/
def tradeCall (orderUid : Uint256) (o : SignedOrder)
    (sellPrice buyPrice executedAmount : Uint256) :
    Contract (Uint256 × Uint256 × Uint256) :=
  GPv2Settlement.computeTradeExecution orderUid o.kind o.partiallyFillable
    o.sellAmount o.buyAmount o.feeAmount o.validTo sellPrice buyPrice executedAmount

/--
Per-trade guarantee. Suppose `computeTradeExecution` succeeds for a signed
order, starting from state `s`. It returns `(inAmount, outAmount, fee)` and
the new state `s'`. Write `sold = inAmount - fee` and `bought = outAmount`.
Then:

1. the in-transfer is exactly `sold + fee` (no hidden extra),
2. `sold * B ≤ bought * S` (limit price respected, after rounding),
3. `filledAmount` grows by exactly the filled part,
4. `filledAmount` after the trade is at most the limit amount (no overfill),
5. `fee * limitAmount ≤ F * filledPart` (fee at most `F` pro rata),
6. the only state change is the write to `filledAmount[orderUid]`.
-/
def trade_execution_spec (orderUid : Uint256) (o : SignedOrder)
    (s s' : ContractState) (inAmount outAmount fee : Uint256) : Prop :=
  let sold := inAmount.val - fee.val
  let bought := outAmount.val
  fee.val ≤ inAmount.val ∧
  respectsLimitPrice o sold bought ∧
  filledOf s' orderUid = filledOf s orderUid + filledPart o sold bought ∧
  filledOf s' orderUid ≤ limitAmount o ∧
  feeWithinSignedFee o fee.val (filledPart o sold bought) ∧
  s' = s.writeMapUint GPv2Settlement.filledAmount.slot orderUid
        (s'.storageMapUint GPv2Settlement.filledAmount.slot orderUid)

/-!
## Token movements

`settle` passes the two computed amounts, unchanged, to `GPv2Transfer`
(`GPv2Settlement.sol` L134 and L138; `GPv2Transfer.sol` L91-L180). There they
go to the token's `transferFrom`/`transfer`, to a Balancer Vault balance
operation, or to a native ETH send. The model does not contain that code or
the token's code. The balance-level guarantee below takes their behaviour as
two explicit hypotheses, one for each transfer of the trade: the pull takes
exactly the amount from the owner (`DebitedExactly`) and the payout gives
exactly the amount to the receiver (`CreditedExactly`). Only the side the
guarantee talks about is assumed, so the hypotheses stay satisfiable when the
owner or receiver is the settlement contract itself.
-/

/-- Balances of one asset (an ERC-20 token, a Balancer Vault internal balance,
or native ETH), by account. -/
abbrev Balances := Address → Nat

/-- **Token hypothesis (pull).** The transfer that pulls `amount` took exactly
`amount` from `acct`. `before` and `after` are balances of the transferred
asset immediately before and after that transfer. -/
def DebitedExactly (before after : Balances) (acct : Address) (amount : Nat) : Prop :=
  after acct + amount = before acct

/-- **Token hypothesis (payout).** The transfer that pays `amount` gave exactly
`amount` to `acct`, with the same before/after convention. Standard ERC-20
tokens, the Balancer Vault and native ETH behave this way; tokens that charge
a fee on transfer or rebase do not. -/
def CreditedExactly (before after : Balances) (acct : Address) (amount : Nat) : Prop :=
  after acct = before acct + amount

/--
Balance-level guarantee for one trade settled through `settle`.

* `paid` = what the owner's sell-token balance dropped by in the transfer that
  pulls this trade's sell amount.
* `received` = what the receiver's buy-token balance rose by in the transfer
  that pays this trade's proceeds.

Then:

1. the owner paid at least the fee: `fee ≤ paid`,
2. the receiver got at least the signed rate:
   `(paid - fee) * B ≤ received * S`,
3. the fee is at most `F` pro rata to the filled part.
-/
def trade_balance_spec (o : SignedOrder) (owner receiver : Address)
    (sellBefore sellAfter buyBefore buyAfter : Balances) (fee : Nat) : Prop :=
  fee ≤ sellBefore owner - sellAfter owner ∧
  respectsLimitPrice o (sellBefore owner - sellAfter owner - fee)
    (buyAfter receiver - buyBefore receiver) ∧
  feeWithinSignedFee o fee
    (filledPart o (sellBefore owner - sellAfter owner - fee)
      (buyAfter receiver - buyBefore receiver))

/-- Running totals over every trade of one order since tracking started. -/
structure OrderTotals where
  sold : Nat
  bought : Nat
  fee : Nat

/--
Every way the state around one order uid can evolve, starting from any
state `s` in which tracking begins. The totals start at zero there, so the
guarantees cover every settle trade of the order made after `s`. For the
complete history of an order, start tracking before its first trade.

* `trade`: a successful `computeTradeExecution` of this order, with any
  solver-chosen prices and executed amount. A uid appearing twice in one
  `settle` batch is two consecutive `trade` steps.
* `invalidate`: a successful `invalidateOrder` of this uid.
* `free`: a successful `freeFilledAmountStorage` of this uid. The `validTo`
  that the Solidity code decodes from the uid is the order's `validTo`,
  because `recoverOrderFromTrade` packs it into the uid.
* `environment`: anything else, including other orders, other uids,
  interactions, and later blocks. It leaves `filledAmount[orderUid]`
  unchanged and never moves `block.timestamp` backwards.
* `swapFill`: the `filledAmount` write at the end of a successful `swap`
  (the Balancer direct path, L217-L230). `swap` fills are not added to the
  settle-path totals, and no claim is made about their price. The step is
  included so that the settle-path guarantees also hold in histories where
  the same order was, or was attempted to be, filled through `swap`.

By source inspection, the writers of `filledAmount` are `swap` (L223,
L229), `invalidateOrder` (L253), `computeTradeExecution` (L421) and
`freeOrderStorage` (L485). This is not mechanized.
-/
inductive OrderLifecycle (orderUid : Uint256) (o : SignedOrder) :
    ContractState → OrderTotals → Prop
  | start (s : ContractState) :
      OrderLifecycle orderUid o s ⟨0, 0, 0⟩
  | trade {s s' : ContractState} {t : OrderTotals}
      (sellPrice buyPrice executedAmount inAmount outAmount fee : Uint256) :
      OrderLifecycle orderUid o s t →
      (tradeCall orderUid o sellPrice buyPrice executedAmount).run s =
        ContractResult.success (inAmount, outAmount, fee) s' →
      OrderLifecycle orderUid o s'
        ⟨t.sold + (inAmount.val - fee.val), t.bought + outAmount.val, t.fee + fee.val⟩
  | invalidate {s s' : ContractState} {t : OrderTotals} (uidOwner : Address) :
      OrderLifecycle orderUid o s t →
      (GPv2Settlement.invalidateOrder orderUid uidOwner).run s =
        ContractResult.success () s' →
      OrderLifecycle orderUid o s' t
  | free {s s' : ContractState} {t : OrderTotals} :
      OrderLifecycle orderUid o s t →
      (GPv2Settlement.freeFilledAmountStorage orderUid o.validTo).run s =
        ContractResult.success () s' →
      OrderLifecycle orderUid o s' t
  | environment {s s' : ContractState} {t : OrderTotals} :
      OrderLifecycle orderUid o s t →
      s'.storageMapUint GPv2Settlement.filledAmount.slot orderUid =
        s.storageMapUint GPv2Settlement.filledAmount.slot orderUid →
      s.blockTimestamp.val ≤ s'.blockTimestamp.val →
      OrderLifecycle orderUid o s' t
  | swapFill {s s' : ContractState} {t : OrderTotals}
      (executedSellAmount executedBuyAmount : Uint256) :
      OrderLifecycle orderUid o s t →
      (GPv2Settlement.swapFilledAmountUpdate orderUid o.kind o.sellAmount o.buyAmount
        executedSellAmount executedBuyAmount).run s = ContractResult.success () s' →
      OrderLifecycle orderUid o s' t

/--
Cumulative guarantee over a tracked lifecycle of one order, for the trades
executed through `settle` since tracking began (see `OrderLifecycle`). Swap
fills are not counted and carry no price or fee claim.

1. `totalSold * B ≤ totalBought * S`: all settle trades together respect the limit price.
2. The total filled part is at most the limit amount: the order is never overfilled.
3. `totalFee * limitAmount ≤ F * totalFilled`: fees stay at most `F` pro rata.

`totalSold` is the executed sell amount excluding fees. The fees are counted
separately in `totalFee`.
-/
def cumulative_order_safety_spec (o : SignedOrder) (t : OrderTotals) : Prop :=
  respectsLimitPrice o t.sold t.bought ∧
  filledPart o t.sold t.bought ≤ limitAmount o ∧
  feeWithinSignedFee o t.fee (filledPart o t.sold t.bought)

/-- Fee cap. For an order with a nonzero limit amount, the total computed fee of
settle-path trades since tracking began is at most the signed `feeAmount`. CoW's README documents that
orders with a zero limit amount can be replayed, computing the fee
repeatedly (see `zero_amount_order_replay`), so they are excluded here. -/
def total_fee_cap_spec (o : SignedOrder) (t : OrderTotals) : Prop :=
  0 < limitAmount o → t.fee ≤ o.feeAmount.val

/-- Zero-fee corollary: for an order signed with `feeAmount = 0` (the production
convention, enforced off-chain by the CoW backend), the settle-path trades
counted since tracking began compute a zero fee (`t.fee = 0`). Token movements and
swap fee transfers are not modeled. -/
def zero_fee_spec (o : SignedOrder) (t : OrderTotals) : Prop :=
  o.feeAmount = 0 → t.fee = 0

/-- The zero-amount sell order behind CoW's README "Known issues". -/
def zeroAmountSellOrder : SignedOrder where
  kind := GPv2Settlement.KIND_SELL
  partiallyFillable := false
  sellAmount := 0
  buyAmount := 0
  feeAmount := 1
  validTo := 100

end Benchmark.Cases.Cow.GPv2Settlement
