import Contracts.Common

namespace Benchmark.Cases.Piku.FundConservation

open Verity hiding pure bind
open Verity.EVM.Uint256

/-
  Verity model of the Piku / Inverter oracle-priced redemption accounting slice.

  Upstream: InverterNetwork/contracts
  Branch/commit used for the Piku docs-matching module:
    origin/dev @ 8b7bc438344d646bab05b751c8eb4a7f0c8ca588

  Solidity files in scope:
  - src/modules/fundingManager/oracle/FM_PC_Oracle_Redeeming_v1.sol
  - src/modules/paymentProcessor/PP_Queue_v1.sol
  - src/modules/paymentProcessor/PP_Queue_ManualExecution_v1.sol
  - src/modules/logicModule/abstracts/ERC20PaymentClientBase_v2.sol

  Piku deployment evidence:
  - Piku docs list Funding Manager 0x7e0305B212dF3FB56366251C054c07748Bf9a797
    as an oracle-priced funding manager with queued redemptions.
  - Piku docs list Payment Processor 0x5A2d08b194E1764b0Ff271C691B6a46fA10F6Fd2
    as a manual queue execution payment processor.
  - Piku docs list Oracle Module 0x433471901bA1A8BDE764E8421790C7D9bAB33552
    as a manual price feed.

  Naming convention:
  - Function and storage names preserve Solidity names where they exist:
    `_sellOrder`, `_createAndEmitOrder`, `_addToOpenRedemptionAmount`,
    `_deductFromOpenRedemptionAmount`, `amountPaid`, `_openRedemptionAmount`,
    `_orderId`, `sellFee`.
  - Loaded local copies of slots take a trailing underscore.
  - The Solidity source does not store cumulative distributed backing, remaining
    backing, or cumulative project/protocol fee counters. Those are modeled as
    ghost accounting slots because the invariant requested by the Piku team is
    a fund-conservation property over economic buckets, while the deployed
    contracts expose only part of those buckets as state.

  Simplifications
  ----------------
  What was simplified:
  - Oracle pricing is represented by an explicit `totalCollateralTokenMovedOut`
    argument to `_sellOrder`.
  Why:
  - `_redeemTokensFormulaWrapper` depends on the external oracle and decimal
    conversion. The conservation transition starts after that value has been
    computed; the invariant is independent of how the oracle price is obtained.

  What was simplified:
  - `projectTreasuryFees`, `protocolTreasuryFees`, `distributedBacking`, and
    `remainingBacking` are ghost accounting slots.
  Why:
  - `FM_PC_Oracle_Redeeming_v1._projectFeeCollected` only emits
    `ProjectCollateralFeeAdded`; it intentionally does not update
    `projectCollateralFeeCollected` because redemption payout is queue-managed.
    `PP_Queue_v1` emits protocol fee transfers but does not keep a cumulative
    protocol-fee counter. These ghosts make the team-proposed conservation
    invariant state-readable without changing the modeled contract control flow.

  What was simplified:
  - Payment-order arrays, linked-list queue structure, event payloads, roles,
    ERC20 balances/allowances, blacklist fallback, and low-level transfer return
    data are omitted.
  Why:
  - The benchmark targets accounting amounts. Queue shape and access control
    decide when a payment can execute, not the conservation arithmetic once a
    valid order exists.

  What was simplified:
  - The payment processor's protocol-fee recalculation
    `amount * protocolFee / (BPS - projectFee)` is modeled by passing the
    already-computed `protocolCollateralFeeAmount` to `amountPaid`.
  Why:
  - The equality between the funding manager's fee split and the payment
    processor's adjusted-denominator split is a separate integer-division
    rounding lemma. This case keeps that as an explicit theorem hypothesis in
    `Proofs.lean` rather than hiding it as an axiom.
  Scope:
  - The `amountPaid` transition models the successful direct-transfer branch of
    `PP_Queue_v1._tryPaymentTransfer`; failed/unclaimable payment accounting is
    out of scope for this conservation slice.

  What was simplified:
  - `remainingBacking` is checked and decremented as a ghost solvency ledger.
  Why:
  - The Solidity `_sellOrder` path checks min-out and queues a payment order;
    it does not store a remaining-backing counter. The guard here is a benchmark
    precondition for the ghost ledger, not a deployed Solidity revert.

  What was simplified:
  - Reverts are represented only by the guards needed for fee validity and
    sufficient remaining backing.
  Why:
  - Other reverts are authorization, receiver, token, oracle-interface, and
    ERC20-transfer checks outside the fund-conservation arithmetic.
-/

def BPS : Uint256 := 10000

def projectFeeAmount (total projectFeeBps : Uint256) : Uint256 :=
  div (mul total projectFeeBps) BPS

def protocolFeeAmount (total protocolFeeBps : Uint256) : Uint256 :=
  div (mul total protocolFeeBps) BPS

def netRedeemAmount (total protocolFeeBps projectFeeBps : Uint256) : Uint256 :=
  sub (sub total (protocolFeeAmount total protocolFeeBps))
    (projectFeeAmount total projectFeeBps)

verity_contract FM_PC_Oracle_Redeeming_v1 where
  storage
    /- Ghost: initial backing committed to the redemption accounting pool. -/
    initialBacking : Uint256 := slot 0

    /- Ghost: backing already distributed to redeeming users. -/
    distributedBacking : Uint256 := slot 1

    /- Ghost: backing not yet distributed, assigned to fees, or queued. -/
    remainingBacking : Uint256 := slot 2

    /- Ghost: collateral fees transferred/accrued to protocol treasury. -/
    protocolTreasuryFees : Uint256 := slot 3

    /- Ghost: collateral fees retained for the Piku/project treasury. -/
    projectTreasuryFees : Uint256 := slot 4

    /- Models `uint internal _openRedemptionAmount;`
       `FM_PC_Oracle_Redeeming_v1.sol:275-278`. -/
    _openRedemptionAmount : Uint256 := slot 5

    /- Models `uint internal _orderId;`
       `FM_PC_Oracle_Redeeming_v1.sol:271-273`. -/
    _orderId : Uint256 := slot 6

    /- Models `uint public sellFee;` inherited from
       `RedeemingBondingCurveBase_v1.sol:63-64`. -/
    sellFee : Uint256 := slot 7

  function _sellOrder
      (totalCollateralTokenMovedOut : Uint256, protocolCollateralSellFeePercentage : Uint256) : Unit := do
    -- src: FM_PC_Oracle_Redeeming_v1.sol:L784-L806 - non-zero and fee metadata checks (scoped)
    let sellFee_ ← getStorage sellFee
    require (totalCollateralTokenMovedOut != 0) "InvalidDepositAmount"
    require (add protocolCollateralSellFeePercentage sellFee_ < 10000) "FeeAmountTooHigh"

    -- src: FM_PC_Oracle_Redeeming_v1.sol:L808-L830 - split collateral into net/protocol/project buckets
    let protocolCollateralFeeAmount :=
      div (mul totalCollateralTokenMovedOut protocolCollateralSellFeePercentage) 10000
    let projectCollateralFeeAmount :=
      div (mul totalCollateralTokenMovedOut sellFee_) 10000
    let netCollateralRedeemAmount :=
      sub (sub totalCollateralTokenMovedOut protocolCollateralFeeAmount) projectCollateralFeeAmount

    -- ghost solvency precondition; source L840-L853 creates the order after min-out check
    let remainingBacking_ ← getStorage remainingBacking
    require (totalCollateralTokenMovedOut <= remainingBacking_) "InsufficientBacking"
    setStorage remainingBacking (sub remainingBacking_ totalCollateralTokenMovedOut)

    -- src: FM_PC_Oracle_Redeeming_v1.sol:L835-L838 and L861-L870 - event-only project fee, ghosted
    let projectTreasuryFees_ ← getStorage projectTreasuryFees
    setStorage projectTreasuryFees (add projectTreasuryFees_ projectCollateralFeeAmount)

    -- src: FM_PC_Oracle_Redeeming_v1.sol:L705-L713 - _orderId++, _openRedemptionAmount += net + protocol
    let _orderId_ ← getStorage _orderId
    setStorage _orderId (add _orderId_ 1)
    let _openRedemptionAmount_ ← getStorage _openRedemptionAmount
    setStorage _openRedemptionAmount
      (add _openRedemptionAmount_ (add netCollateralRedeemAmount protocolCollateralFeeAmount))

  function amountPaid (amount : Uint256, protocolCollateralFeeAmount : Uint256) : Unit := do
    -- src: PP_Queue_v1.sol:L656-L717 - successful queue transfer and amountPaid callback
    let _openRedemptionAmount_ ← getStorage _openRedemptionAmount
    require (amount <= _openRedemptionAmount_) "OpenRedemptionUnderflow"
    require (protocolCollateralFeeAmount <= amount) "InvalidProtocolFee"

    -- src: FM_PC_Oracle_Redeeming_v1.sol:L608-L616 and L1026-L1031 - deduct processed amount
    setStorage _openRedemptionAmount (sub _openRedemptionAmount_ amount)

    -- src: PP_Queue_v1.sol:L673-L695 - net to recipient, protocol fee to treasury (ghosted)
    let distributedBacking_ ← getStorage distributedBacking
    setStorage distributedBacking (add distributedBacking_ (sub amount protocolCollateralFeeAmount))
    let protocolTreasuryFees_ ← getStorage protocolTreasuryFees
    setStorage protocolTreasuryFees (add protocolTreasuryFees_ protocolCollateralFeeAmount)

end Benchmark.Cases.Piku.FundConservation
