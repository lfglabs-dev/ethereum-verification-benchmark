/-
Source-structured, proof-only model of KpkShares.processRequests, source revision
714d3d66a6e0e2bc7849ae48c3a25f63f23e903f. Not an automatic import or compilation.
Simplifications / applicability boundaries:
* KPK structs/configuration and inherited ERC20 storage are logical projections,
  not a claim about packed slots, Keccak collision resistance or ERC7201 refinement.
  There is ONE inherited share ledger in Verity.ContractState, no parallel supply.
* Asset calls execute a conventional no-tax/no-rebase ERC20 body with allowance
  spending and debit-before-recipient-reload. ExternalWorld cells are a projection.
  SafeERC20 return encoding is restricted to bool true or empty/code-bearing tokens;
  arbitrary malformed ABI, logs, gas, revert bytes and callbacks are not refined.
* A mutable fee responder receives the actual arguments/current module world;
  it can fail, mutate its own state or return a bounded fee. It cannot mutate caller
  or token state. Module selector dispatch at known token/KPK addresses fails.
  This is an interface/no-callback restriction, NOT a source reentrancy guard.
* Lists model ordered ABI arrays, with genuine structural recursion. No body-once
  shallow loops, no unrolling, no deduplication, no no-op payment wrappers.
* Uint256 arithmetic uses Verity checked primitives; Nat projections have explicit
  range premises. Source unchecked ledger credits wrap, matching OZ _update.
* Initialization/intake/cancellation/recovery/admin/upgrades, metadata strings,
  arbitrary external share transfers, fee-module economics and NAV are excluded.
* Trace entries are observations appended AFTER actual effects, not substitute
  effects or assumptions of correct accounting. Whole-world failure rollback is real.
-/
import Verity.Core
import Verity.Stdlib.Math
import Verity.Core.Model.ECM

namespace Benchmark.Cases.KPK.SharesSettlementAccounting
open Verity Verity.Stdlib.Math
open Compiler.ECM.StatefulExternal
set_option maxHeartbeats 2000000

def wordLimit : Nat := 2^256
def wad : Nat := 10^18
def usd : Nat := 10^8
def bps : Nat := 10000

def word (n : Nat) : Uint256 := Verity.Core.Uint256.ofNat n

def balanceSlot : StorageSlot (Address → Uint256) := ⟨0⟩
def allowanceSlot : StorageSlot (Address → Address → Uint256) := ⟨1⟩
def supplySlot : StorageSlot Uint256 := ⟨2⟩

inductive RequestType where | subscription | redemption deriving BEq, DecidableEq, Repr
inductive RequestStatus where | pending | processed | rejected | cancelled deriving BEq, DecidableEq, Repr
structure UserRequest where
  requestType : RequestType := .subscription
  requestStatus : RequestStatus := .pending
  asset : Address := 0
  assetAmount : Nat := 0
  sharesAmount : Nat := 0
  investor : Address := 0
  receiver : Address := 0
  timestamp : Nat := 0
  expiryAt : Nat := 0
  deriving Inhabited, DecidableEq
structure ApprovedAsset where
  asset : Address := 0
  decimals : Nat := 0
  isFeeModuleAsset : Bool := false
  canDeposit : Bool := false
  canRedeem : Bool := false
  deriving Inhabited
structure Configuration where
  self : Address
  portfolioSafe : Address
  feeReceiver : Address
  performanceFeeModule : Address
  managementFeeRate : Nat
  redemptionFeeRate : Nat
  performanceFeeRate : Nat
  assets : Address → ApprovedAsset
  operators : Address → Bool

inductive Effect where
  | mint (to : Address) (amount : Nat)
  | burn (fromAddr : Address) (amount : Nat)
  | shareTransfer (fromAddr to : Address) (amount : Nat)
  | assetTransfer (asset fromAddr to : Address) (amount : Nat)
  | allowanceSpent (asset owner spender : Address) (amount : Nat)
  | management (amount : Nat)
  | performance (amount : Nat)
  | moduleCall (target : Address) (price elapsed rate netSupply result : Nat)
  | subscription (id : Nat) (request : UserRequest) (minted : Nat)
  | redemption (id : Nat) (request : UserRequest) (fee net payout : Nat)
  | rejection (id : Nat) (request : UserRequest)
  deriving DecidableEq

structure State where
  caller : ContractState
  external : ExternalWorld
  config : Configuration
  requests : Nat → UserRequest
  subscriptionAssets : Address → Nat
  pendingRequestsCount : Address → Nat
  managementFeeLastUpdate : Nat
  performanceFeeLastUpdate : Nat
  lastSettledPrice : Address → Nat
  trace : List Effect := []

abbrev Tx := StateT State (Except String)
structure FeeArgs where
  target : Address
  caller : Address
  price : Nat
  elapsed : Nat
  rate : Nat
  netSupply : Nat
-- A typed mutable callee interface. Returned storage belongs only to this module;
-- the adapter inserts it at target, preserving every other world's address.
abbrev FeeResponder := FeeArgs → (Nat → Nat) → Except String (Nat × (Nat → Nat))
structure Environment where
  sender : Address
  now : Nat
  hasCode : Address → Bool
  isToken : Address → Bool
  tokenAccepts : Address → Bool
  feeResponder : FeeResponder

def liftCaller (c : Contract α) : Tx α := fun s =>
  match c s.caller with
  | .success a c' => .ok (a, {s with caller := c'})
  | .revert e _ => .error e

def record (e : Effect) : Tx Unit := modify fun s => {s with trace := s.trace ++ [e]}
def guard (p : Bool) (e : String) : Tx Unit := if p then pure () else throw e

def checkedAdd (a b : Nat) : Tx Nat := do
  return (← liftCaller (addPanic (word a) (word b))).val

def checkedSub (a b : Nat) : Tx Nat := do
  return (← liftCaller (subPanic (word a) (word b))).val

def checkedMul (a b : Nat) : Tx Nat := do
  return (← liftCaller (mulPanic (word a) (word b))).val

def mulDiv (a b d : Nat) : Tx Nat := do
  return (← liftCaller (requireSomeUint (mulDiv512Down? (word a) (word b) (word d)) "mulDiv overflow/division" )).val

def shareBalance (s : State) (a : Address) : Nat := (s.caller.readMap balanceSlot.slot a).val
def totalSupply (s : State) : Nat := (s.caller.readSlot supplySlot.slot).val

def _update (fromAddr to : Address) (amount : Nat) : Tx Unit := do
  if fromAddr == 0 then
    let t ← liftCaller (getStorage supplySlot)
    let next ← liftCaller (addPanic t (word amount))
    liftCaller (setStorage supplySlot next)
  else
    let old ← liftCaller (getMapping balanceSlot fromAddr)
    guard (old.val >= amount) "ERC20InsufficientBalance"
    liftCaller (setMapping balanceSlot fromAddr (word (old.val - amount)))
  if to == 0 then
    let t ← liftCaller (getStorage supplySlot)
    -- Source unchecked subtraction; coherent inherited ledger is a premise.
    liftCaller (setStorage supplySlot (t - word amount))
  else
    -- Source reload after debit is necessary for self-transfer.
    let old ← liftCaller (getMapping balanceSlot to)
    liftCaller (setMapping balanceSlot to (old + word amount))

def _mint (to : Address) (amount : Nat) : Tx Unit := do
  guard (to != 0) "ERC20InvalidReceiver"
  _update 0 to amount
  record (.mint to amount)
def _burn (fromAddr : Address) (amount : Nat) : Tx Unit := do
  guard (fromAddr != 0) "ERC20InvalidSender"
  _update fromAddr 0 amount
  record (.burn fromAddr amount)
def _transfer (fromAddr to : Address) (amount : Nat) : Tx Unit := do
  guard (fromAddr != 0) "ERC20InvalidSender"
  guard (to != 0) "ERC20InvalidReceiver"
  _update fromAddr to amount
  record (.shareTransfer fromAddr to amount)

-- Conventional token projection, tagged address/allowance cells via Cantor pairing.
def bslot (a : Address) : Nat := 2 * a.val
def aslot (a b : Address) : Nat :=
  2 * (((a.val + b.val) * (a.val + b.val + 1)) / 2 + b.val) + 1

def assetBalance (s : State) (token owner : Address) : Nat := s.external.accountState token.val (bslot owner)
def assetAllowance (s : State) (token owner spender : Address) : Nat := s.external.accountState token.val (aslot owner spender)
def writeExternal (w : ExternalWorld) (target slot value : Nat) : ExternalWorld :=
  {accountState := fun t k => if t == target && k == slot then value else w.accountState t k}
def putExternal (token : Address) (slot value : Nat) : Tx Unit :=
  modify fun s => {s with external := writeExternal s.external token.val slot value}

def safeTransfer (env : Environment) (token fromAddr to : Address) (amount : Nat) : Tx Unit := do
  let s ← get
  guard (env.hasCode token && env.isToken token && env.tokenAccepts token) "SafeERC20FailedOperation"
  guard (token != s.config.self) "non-self approved asset premise"
  guard (fromAddr != 0 && to != 0) "token zero endpoint"
  let old := assetBalance s token fromAddr
  let next ← checkedSub old amount
  putExternal token (bslot fromAddr) next
  let recipient := assetBalance (← get) token to
  -- Conventional OZ token credit is unchecked; ledger coherence belongs in
  -- applicability for the unwrapped exact-payment theorem, not a fake guard.
  putExternal token (bslot to) (word (recipient + amount)).val
  record (.assetTransfer token fromAddr to amount)

def safeTransferFrom (env : Environment) (token spender fromAddr to : Address) (amount : Nat) : Tx Unit := do
  let available := assetAllowance (← get) token fromAddr spender
  if available != wordLimit - 1 then
    let next ← checkedSub available amount
    putExternal token (aslot fromAddr spender) next
    record (.allowanceSpent token fromAddr spender amount)
  safeTransfer env token fromAddr to amount

def assetsToShares (amount price : Nat) (asset : Address) : Tx Nat := do
  if price == 0 || amount == 0 then return 0
  let cfg := (← get).config.assets asset
  guard cfg.canDeposit "NotAnApprovedAsset"
  let value ← mulDiv amount (wad * wad) price
  let scale ← checkedMul (10^cfg.decimals) wad
  mulDiv value usd scale

def sharesToAssets (shares price : Nat) (asset : Address) : Tx Nat := do
  if price == 0 || shares == 0 then return 0
  let cfg := (← get).config.assets asset
  guard cfg.canRedeem "UnredeemableAsset"
  let priceWad ← checkedMul price wad
  let value ← mulDiv shares priceWad usd
  mulDiv value (10^cfg.decimals) (wad * wad)

def setStatus (id : Nat) (status : RequestStatus) : Tx Unit := do
  let req := (← get).requests id
  modify fun s => {s with requests := fun j => if j == id then {req with requestStatus := status} else s.requests j}

def decrementCount (asset : Address) : Tx Unit := do
  let next ← checkedSub ((← get).pendingRequestsCount asset) 1
  modify fun s => {s with pendingRequestsCount := fun a => if a == asset then next else s.pendingRequestsCount a}
def debitSubscription (asset : Address) (amount : Nat) : Tx Unit := do
  let next ← checkedSub ((← get).subscriptionAssets asset) amount
  modify fun s => {s with subscriptionAssets := fun a => if a == asset then next else s.subscriptionAssets a}

def _approveSubscriptionRequest (env : Environment) (id : Nat) (request : UserRequest) (price : Nat) : Tx Unit := do
  let sharesOut ← assetsToShares request.assetAmount price request.asset
  guard (sharesOut >= request.sharesAmount) "RequestPriceLowerThanOperatorPrice"
  setStatus id .processed
  debitSubscription request.asset request.assetAmount
  decrementCount request.asset
  _mint request.receiver sharesOut
  let cfg := (← get).config
  safeTransfer env request.asset cfg.self cfg.portfolioSafe request.assetAmount
  record (.subscription id request sharesOut)

def _rejectSubscriptionRequest (env : Environment) (id : Nat) (request : UserRequest) : Tx Unit := do
  setStatus id .rejected
  debitSubscription request.asset request.assetAmount
  decrementCount request.asset
  safeTransfer env request.asset (← get).config.self request.investor request.assetAmount
  record (.rejection id request)

def _chargeRedemptionFee (request : UserRequest) : Tx Nat := do
  let cfg := (← get).config
  let prod ← checkedMul request.sharesAmount cfg.redemptionFeeRate
  let fee := prod / bps
  if fee > 0 then _transfer cfg.self cfg.feeReceiver fee
  return fee

def _approveRedeemRequest (env : Environment) (id : Nat) (request : UserRequest) (price : Nat) : Tx Unit := do
  let cfg := (← get).config
  let fee ← if cfg.redemptionFeeRate > 0 then _chargeRedemptionFee request else pure 0
  let net ← checkedSub request.sharesAmount fee
  let payout ← sharesToAssets net price request.asset
  guard (payout >= request.assetAmount) "RequestPriceLowerThanOperatorPrice"
  setStatus id .processed
  decrementCount request.asset
  _burn cfg.self net
  safeTransferFrom env request.asset cfg.self cfg.portfolioSafe request.receiver payout
  record (.redemption id request fee net payout)

def _rejectRedeemRequest (id : Nat) (request : UserRequest) : Tx Unit := do
  setStatus id .rejected
  decrementCount request.asset
  _transfer (← get).config.self request.investor request.sharesAmount
  record (.rejection id request)

def _checkValidRequest (request : UserRequest) : Bool :=
  request.investor != 0 && request.requestStatus == .pending

def approveOne (env : Environment) (asset : Address) (price id : Nat) : Tx Unit := do
  let request := (← get).requests id
  if !_checkValidRequest request then return ()
  if request.asset != asset then return ()
  if env.now > request.expiryAt then
    if request.requestType == .subscription then _rejectSubscriptionRequest env id request
    else _rejectRedeemRequest id request
  else if request.requestType == .subscription then _approveSubscriptionRequest env id request price
  else _approveRedeemRequest env id request price

def rejectOne (env : Environment) (asset : Address) (id : Nat) : Tx Unit := do
  let request := (← get).requests id
  if !_checkValidRequest request then return ()
  if request.asset != asset then return ()
  if request.requestType == .subscription then _rejectSubscriptionRequest env id request
  else _rejectRedeemRequest id request

def iterate (body : Nat → Tx Unit) : List Nat → Tx Unit
  | [] => pure ()
  | id :: ids => do body id; iterate body ids

def _processApproved (env : Environment) (ids : List Nat) (asset : Address) (price : Nat) : Tx Unit :=
  iterate (approveOne env asset price) ids

def _processRejected (env : Environment) (ids : List Nat) (asset : Address) : Tx Unit :=
  iterate (rejectOne env asset) ids

def _validatePriceDeviation (asset : Address) (price : Nat) : Tx Unit := do
  let last := (← get).lastSettledPrice asset
  if last == 0 then return ()
  let deviation := if price > last then price - last else last - price
  let deviationBps ← mulDiv deviation bps last
  guard (deviationBps <= 3000) "PriceDeviationTooLarge"

def _chargeManagementFee (elapsed : Nat) : Tx Nat := do
  let s ← get
  let net ← checkedSub (totalSupply s) (shareBalance s s.config.feeReceiver)
  let annual ← checkedMul net s.config.managementFeeRate
  let product ← checkedMul annual elapsed
  let fee := product / (bps * 31536000)
  if fee > 0 then _mint s.config.feeReceiver fee
  record (.management fee)
  return fee

def _chargePerformanceFee (env : Environment) (price elapsed : Nat) : Tx Nat := do
  let s ← get
  let cfg := s.config
  if cfg.performanceFeeModule == 0 then return 0
  let net ← checkedSub (totalSupply s) (shareBalance s cfg.feeReceiver)
  -- Known ERC20/KPK contracts do not implement the performance selector. Other
  -- modules are modeled by the typed mutable interface under callback framing.
  guard (env.hasCode cfg.performanceFeeModule) "module code/decode failure"
  guard (cfg.performanceFeeModule != cfg.self && !(env.isToken cfg.performanceFeeModule)) "module selector dispatch"
  let args : FeeArgs := ⟨cfg.performanceFeeModule, cfg.self, price, elapsed, cfg.performanceFeeRate, net⟩
  match env.feeResponder args (s.external.accountState cfg.performanceFeeModule.val) with
  | .error err => throw err
  | .ok (fee, moduleState) =>
    guard (fee < wordLimit) "module uint256 decode"
    modify fun st => {st with external := {accountState := fun t k =>
      if t == cfg.performanceFeeModule.val then moduleState k else st.external.accountState t k}}
    record (.moduleCall cfg.performanceFeeModule price elapsed cfg.performanceFeeRate net fee)
    if fee > 0 then _mint cfg.feeReceiver fee
    record (.performance fee)
    return fee

def _chargeFees (env : Environment) (asset : Address) (price : Nat) : Tx Unit := do
  let cfg := (← get).config
  if cfg.managementFeeRate > 0 then
    let elapsed ← checkedSub env.now (← get).managementFeeLastUpdate
    if elapsed > 21600 then
      modify fun s => {s with managementFeeLastUpdate := env.now}
      let _ ← _chargeManagementFee elapsed
  if cfg.performanceFeeRate > 0 && (cfg.assets asset).isFeeModuleAsset then
    let elapsed ← checkedSub env.now (← get).performanceFeeLastUpdate
    if elapsed > 21600 then
      modify fun s => {s with performanceFeeLastUpdate := env.now}
      let _ ← _chargePerformanceFee env price elapsed

def processRequests (env : Environment) (approved rejected : List Nat) (asset : Address) (price : Nat) : Tx Unit := do
  guard ((← get).config.operators env.sender) "NotAuthorized"
  _validatePriceDeviation asset price
  _chargeFees env asset price
  _processApproved env approved asset price
  _processRejected env rejected asset
  modify fun s => {s with lastSettledPrice := fun a => if a == asset then price else s.lastSettledPrice a}

-- Transaction-wide rollback, including previous requests, all fee mints and module
-- mutations; a failed item does not merely rollback its own local effects.
def transaction (c : Tx α) (s : State) : Except String (α × State) × State :=
  match c s with
  | .ok (a, next) => (.ok (a, next), next)
  | .error err => (.error err, s)
end Benchmark.Cases.KPK.SharesSettlementAccounting
