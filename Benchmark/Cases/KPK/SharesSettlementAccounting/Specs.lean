import Benchmark.Cases.KPK.SharesSettlementAccounting.Contract

namespace Benchmark.Cases.KPK.SharesSettlementAccounting
open Verity

/-! ONE full-batch accounting specification. The starting-state premises are not
certified historical reachability. Expected amounts and effects below depend on
recorded inputs/price, not on final supply or token balance differences. -/

def Mint (amount price decimals : Nat) : Nat :=
  if price = 0 ∨ amount = 0 then 0
  else ((amount * (wad * wad)) / price * usd) / (10^decimals * wad)
def Out (net price decimals : Nat) : Nat :=
  if price = 0 ∨ net = 0 then 0
  else ((net * (price * wad)) / usd * 10^decimals) / (wad * wad)
def RedeemFee (shares rate : Nat) : Nat := shares * rate / bps

def allocated (n : Nat) : List Nat := List.range n

def SubLiability (s : State) (n : Nat) (asset : Address) : Nat :=
  ((allocated n).map fun id => let r := s.requests id
    if _checkValidRequest r && r.asset == asset && r.requestType == .subscription
    then r.assetAmount else 0).sum

def RedLiability (s : State) (n : Nat) : Nat :=
  ((allocated n).map fun id => let r := s.requests id
    if _checkValidRequest r && r.requestType == .redemption then r.sharesAmount else 0).sum

def PendingCount (s : State) (n : Nat) (asset : Address) : Nat :=
  ((allocated n).filter fun id => let r := s.requests id
    _checkValidRequest r && r.asset == asset).length

def Payload (a b : UserRequest) : Prop :=
  a.requestType = b.requestType ∧ a.asset = b.asset ∧
  a.assetAmount = b.assetAmount ∧ a.sharesAmount = b.sharesAmount ∧
  a.investor = b.investor ∧ a.receiver = b.receiver ∧
  a.timestamp = b.timestamp ∧ a.expiryAt = b.expiryAt

def LedgerCoherent (s : State) : Prop :=
  ∃ accounts : List Address, accounts.Nodup ∧
    (∀ a, a ∉ accounts → shareBalance s a = 0) ∧
    (accounts.map (shareBalance s)).sum = totalSupply s ∧ shareBalance s 0 = 0

def RecordsConsistent (s : State) (n : Nat) : Prop :=
  (∀ a, s.subscriptionAssets a = SubLiability s n a) ∧
  (∀ a, s.pendingRequestsCount a = PendingCount s n a)

def WellFormed (env : Environment) (s : State) (n : Nat) : Prop :=
  s.trace = [] ∧ LedgerCoherent s ∧ RecordsConsistent s n ∧
  n ≤ wordLimit ∧ s.requests 0 = default ∧ env.now < wordLimit ∧
  s.config.self ≠ 0 ∧ s.config.portfolioSafe ≠ 0 ∧ s.config.feeReceiver ≠ 0 ∧
  s.config.managementFeeRate ≤ 2000 ∧ s.config.redemptionFeeRate ≤ 2000 ∧
  s.config.performanceFeeRate ≤ 2000 ∧
  s.managementFeeLastUpdate < wordLimit ∧ s.performanceFeeLastUpdate < wordLimit ∧
  (∀ a, s.lastSettledPrice a < wordLimit) ∧
  (∀ a, s.subscriptionAssets a < wordLimit ∧ s.pendingRequestsCount a < wordLimit) ∧
  (∀ a, (s.config.assets a).decimals ≤ 36 ∧
    ((s.config.assets a).asset ≠ 0 → (s.config.assets a).asset = a ∧ a ≠ s.config.self) ∧
    ((s.config.assets a).asset = 0 → (s.config.assets a).canDeposit = false ∧
      (s.config.assets a).canRedeem = false ∧ (s.config.assets a).isFeeModuleAsset = false)) ∧
  (∀ token owner, assetBalance s token owner < wordLimit) ∧
  (∀ token owner spender, assetAllowance s token owner spender < wordLimit) ∧
  (∀ id, id ≥ n → s.requests id = default) ∧
  (∀ id, id < n → let r := s.requests id
    r.assetAmount < wordLimit ∧ r.sharesAmount < wordLimit ∧
    r.timestamp < 2^64 ∧ r.expiryAt < 2^64 ∧
    (r = default ∨ (r.investor ≠ 0 ∧ r.receiver ≠ 0 ∧ r.assetAmount > 0 ∧ r.sharesAmount > 0 ∧
    r.asset ≠ 0 ∧ r.asset ≠ s.config.self ∧
    (r.requestStatus = .pending → (s.config.assets r.asset).asset = r.asset))) ) ∧
  (∀ a, assetBalance s a s.config.self ≥ SubLiability s n a) ∧
  shareBalance s s.config.self ≥ RedLiability s n

-- Business effects extracted from high-level settlement records, not the primitive
-- mint/transfer trace. This independent expansion catches omitted/wrong transfers.
inductive Payment where
  | mint (to : Address) (amount : Nat)
  | burn (fromAddr : Address) (amount : Nat)
  | share (fromAddr to : Address) (amount : Nat)
  | asset (token fromAddr to : Address) (amount : Nat)
  deriving DecidableEq

def actualPayments : List Effect → List Payment
  | [] => []
  | e :: es => (match e with
    | .mint to a => [.mint to a]
    | .burn fromAddr a => [.burn fromAddr a]
    | .shareTransfer fromAddr to a => [.share fromAddr to a]
    | .assetTransfer token fromAddr to a => [.asset token fromAddr to a]
    | _ => []) ++ actualPayments es

def expectedPayments (cfg : Configuration) : List Effect → List Payment
  | [] => []
  | e :: es => (match e with
    | .management a => if a > 0 then [.mint cfg.feeReceiver a] else []
    | .performance a => if a > 0 then [.mint cfg.feeReceiver a] else []
    | .subscription _ r m => [.mint r.receiver m, .asset r.asset cfg.self cfg.portfolioSafe r.assetAmount]
    | .redemption _ r fee net payout =>
      (if fee > 0 then [.share cfg.self cfg.feeReceiver fee] else []) ++
      [.burn cfg.self net, .asset r.asset cfg.portfolioSafe r.receiver payout]
    | .rejection _ r => if r.requestType == .subscription
      then [.asset r.asset cfg.self r.investor r.assetAmount]
      else [.share cfg.self r.investor r.sharesAmount]
    | _ => []) ++ expectedPayments cfg es

def consumed : List Effect → List Nat
  | [] => []
  | e :: es => (match e with
    | .subscription id _ _ | .redemption id _ _ _ _ | .rejection id _ => [id]
    | _ => []) ++ consumed es

def supplyEffect : Payment → Int
  | .mint _ a => a
  | .burn _ a => -(a : Int)
  | _ => 0

def indicator (x y : Address) (a : Nat) : Int := if x = y then a else 0

def shareEffect (x : Address) : Payment → Int
  | .mint to a => indicator x to a
  | .burn fromAddr a => -indicator x fromAddr a
  | .share fromAddr to a => indicator x to a - indicator x fromAddr a
  | _ => 0

def assetEffect (token x : Address) : Payment → Int
  | .asset t fromAddr to a => if token = t then indicator x to a - indicator x fromAddr a else 0
  | _ => 0

def Balanced (before after : State) : Prop :=
  let payments := expectedPayments before.config after.trace
  (totalSupply after : Int) - totalSupply before = (payments.map supplyEffect).sum ∧
  (∀ x, (shareBalance after x : Int) - shareBalance before x = (payments.map (shareEffect x)).sum) ∧
  (∀ token x, envToken token →
    (assetBalance after token x : Int) - assetBalance before token x = (payments.map (assetEffect token x)).sum)
where
  -- Exclude mutable-module-owned storage from ERC20 balance claims. Token addresses
  -- in the initial registered asset projection are the accounting vector domain.
  envToken (token : Address) : Prop := (before.config.assets token).asset = token ∧ token ≠ 0

def ConversionCorrect (cfg : Configuration) (price : Nat) : Effect → Prop
  | .subscription _ r m =>
    m = Mint r.assetAmount price (cfg.assets r.asset).decimals ∧ m ≥ r.sharesAmount ∧
    (price > 0 → m * price * 10^(cfg.assets r.asset).decimals ≤ r.assetAmount * wad * usd ∧
      r.assetAmount * wad * usd < (m+1) * price * 10^(cfg.assets r.asset).decimals)
  | .redemption _ r fee net payout =>
    fee = RedeemFee r.sharesAmount cfg.redemptionFeeRate ∧ net = r.sharesAmount - fee ∧
    payout = Out net price (cfg.assets r.asset).decimals ∧ payout ≥ r.assetAmount ∧
    (price > 0 → payout * wad * usd ≤ net * price * 10^(cfg.assets r.asset).decimals ∧
      net * price * 10^(cfg.assets r.asset).decimals < (payout+1) * wad * usd)
  | _ => True

-- Callee framing prevents module-owned mutations from pretending to be token
-- balance updates. Registered asset targets are conventional ERC20 targets.
def ExternalApplicability (env : Environment) (s : State) : Prop :=
  ∀ a, (s.config.assets a).asset = a → a ≠ 0 →
    env.hasCode a = true ∧ env.isToken a = true ∧
    (∃ accounts : List Address, accounts.Nodup ∧
      (∀ owner, owner ∉ accounts → assetBalance s a owner = 0) ∧
      (accounts.map (assetBalance s a)).sum < wordLimit ∧ assetBalance s a 0 = 0)

structure Decision where
  id : Nat
  status : RequestStatus
  deriving DecidableEq

def actualDecisions : List Effect → List Decision
  | [] => []
  | e :: es => (match e with
    | .subscription id _ _ | .redemption id _ _ _ _ => [⟨id, .processed⟩]
    | .rejection id _ => [⟨id, .rejected⟩]
    | _ => []) ++ actualDecisions es

-- Independent input traversal. Shadow only statuses; do not execute payment code.
def selectDecisions (before : State) (now : Nat) (asset : Address)
    (approve : Bool) : List Nat → (Nat → RequestStatus) → List Decision
  | [], _ => []
  | id :: ids, statuses =>
    let r := before.requests id
    if r.investor != 0 && statuses id == .pending && r.asset == asset then
      let status := if approve && now <= r.expiryAt then .processed else .rejected
      ⟨id, status⟩ :: selectDecisions before now asset approve ids
        (fun j => if j == id then status else statuses j)
    else selectDecisions before now asset approve ids statuses

def expectedDecisions (before : State) (now : Nat) (asset : Address)
    (approved rejected : List Nat) : List Decision :=
  let first := selectDecisions before now asset true approved (fun id => (before.requests id).requestStatus)
  let updated := fun id => if (first.map Decision.id).contains id then .processed else (before.requests id).requestStatus
  first ++ selectDecisions before now asset false rejected updated

def feeSum (management : Bool) (trace : List Effect) : Nat :=
  (trace.map fun e => match e with
    | .management a => if management then a else 0
    | .performance a => if management then 0 else a
    | _ => 0).sum

def ExpectedManagement (before : State) (now : Nat) : Nat :=
  if before.config.managementFeeRate > 0 ∧ now - before.managementFeeLastUpdate > 21600 then
    ((totalSupply before - shareBalance before before.config.feeReceiver) * before.config.managementFeeRate *
      (now - before.managementFeeLastUpdate)) / (bps * 31536000)
  else 0

structure FeeReceipt where
  trace : List Effect
  world : Compiler.ECM.StatefulExternal.ExternalWorld
  managementTime : Nat
  performanceTime : Nat

def natSub (a b : Nat) : Except String Nat :=
  if b > a then .error "underflow" else .ok (a-b)
def natMul (a b : Nat) : Except String Nat :=
  if a*b >= wordLimit then .error "overflow" else .ok (a*b)
def natCheck (p : Bool) : Except String Unit :=
  if p then .ok () else .error "fee precondition"

-- Independent fee prefix. Its responder is evaluated against the ORIGINAL module
-- state and exact source arguments, not a result invented in an observation.
def expectedFeePrefix (env : Environment) (before : State) (asset : Address) (price : Nat) : Except String FeeReceipt := do
  let cfg := before.config
  let elapsed ← if cfg.managementFeeRate > 0 then natSub env.now before.managementFeeLastUpdate else pure 0
  let activeM := cfg.managementFeeRate > 0 && elapsed > 21600
  let g ← if activeM then do
    let net ← natSub (totalSupply before) (shareBalance before cfg.feeReceiver)
    let annual ← natMul net cfg.managementFeeRate
    let prod ← natMul annual elapsed
    pure (prod / (bps * 31536000))
    else pure 0
  natCheck (totalSupply before + g < wordLimit)
  let mt := if activeM then env.now else before.managementFeeLastUpdate
  let feeTracePart := if activeM then (if g > 0 then [Effect.mint cfg.feeReceiver g] else []) ++ [.management g] else []
  let enabled := cfg.performanceFeeRate > 0 && (cfg.assets asset).isFeeModuleAsset
  let perfElapsed ← if enabled then natSub env.now before.performanceFeeLastUpdate else pure 0
  let activeP := enabled && perfElapsed > 21600
  let pt := if activeP then env.now else before.performanceFeeLastUpdate
  if !activeP || cfg.performanceFeeModule == 0 then
    return ⟨feeTracePart, before.external, mt, pt⟩
  natCheck (env.hasCode cfg.performanceFeeModule && cfg.performanceFeeModule != cfg.self && !env.isToken cfg.performanceFeeModule)
  let net ← natSub (totalSupply before + g) (shareBalance before cfg.feeReceiver + g)
  let args : FeeArgs := ⟨cfg.performanceFeeModule,cfg.self,price,perfElapsed,cfg.performanceFeeRate,net⟩
  let (h, moduleState) ← env.feeResponder args (before.external.accountState cfg.performanceFeeModule.val)
  natCheck (h < wordLimit && totalSupply before + g + h < wordLimit)
  let world : Compiler.ECM.StatefulExternal.ExternalWorld :=
    {accountState := fun t k => if t == cfg.performanceFeeModule.val then moduleState k else before.external.accountState t k}
  return ⟨feeTracePart ++ [.moduleCall cfg.performanceFeeModule price perfElapsed cfg.performanceFeeRate net h] ++
    (if h > 0 then [.mint cfg.feeReceiver h] else []) ++ [.performance h], world, mt, pt⟩

def isFeeMarker : Effect → Bool
  | .management _ | .performance _ | .moduleCall _ _ _ _ _ _ => true
  | _ => false

def tokenWordTransfer (w : Compiler.ECM.StatefulExternal.ExternalWorld)
    (token fromAddr to : Address) (amount : Nat) : Compiler.ECM.StatefulExternal.ExternalWorld :=
  let debited := writeExternal w token.val (bslot fromAddr) (w.accountState token.val (bslot fromAddr) - amount)
  writeExternal debited token.val (bslot to) (word (debited.accountState token.val (bslot to) + amount)).val

def expectedWorldStep (cfg : Configuration)
    (w : Compiler.ECM.StatefulExternal.ExternalWorld) (e : Effect) : Compiler.ECM.StatefulExternal.ExternalWorld :=
  match e with
  | .subscription _ r _ => tokenWordTransfer w r.asset cfg.self cfg.portfolioSafe r.assetAmount
  | .redemption _ r _ _ payout =>
    let available := w.accountState r.asset.val (aslot cfg.portfolioSafe cfg.self)
    let next := if available = wordLimit-1 then w else
      writeExternal w r.asset.val (aslot cfg.portfolioSafe cfg.self) (available - payout)
    tokenWordTransfer next r.asset cfg.portfolioSafe r.receiver payout
  | .rejection _ r => if r.requestType == .subscription then
      tokenWordTransfer w r.asset cfg.self r.investor r.assetAmount else w
  | _ => w

-- Exact module mutation, token movements, untouched targets/cells and source fee
-- prefix order are connected to an independent world replay. Trace amounts are
-- additionally fixed by ConversionCorrect and original request payloads.
def FeeCorrect (env : Environment) (before after : State) (asset : Address) (price : Nat) : Prop :=
  ∃ receipt suffix, expectedFeePrefix env before asset price = .ok receipt ∧
    after.trace = receipt.trace ++ suffix ∧ (∀ e, e ∈ suffix → isFeeMarker e = false) ∧
    after.managementFeeLastUpdate = receipt.managementTime ∧
    after.performanceFeeLastUpdate = receipt.performanceTime ∧
    after.external.accountState = (suffix.foldl (expectedWorldStep before.config) receipt.world).accountState

-- Caller channels unused by this settlement remain unchanged. knownAddresses at
-- the balance slot is Verity bookkeeping, not a Solidity field and may grow.
def CallerFrame (before after : State) (asset : Address) : Prop :=
  (∀ a, a ≠ asset → after.lastSettledPrice a = before.lastSettledPrice a) ∧
  (∀ slot, slot ≠ supplySlot.slot → after.caller.readSlot slot = before.caller.readSlot slot) ∧
  (∀ slot a, slot ≠ balanceSlot.slot → after.caller.readMap slot a = before.caller.readMap slot a) ∧
  after.caller.storageMap2 = before.caller.storageMap2 ∧
  after.caller.storageMapUint = before.caller.storageMapUint ∧
  after.caller.storageAddr = before.caller.storageAddr ∧
  after.caller.storageArray = before.caller.storageArray ∧
  after.caller.transientStorage = before.caller.transientStorage ∧
  after.caller.memory = before.caller.memory ∧ after.caller.events = before.caller.events ∧
  after.caller.sender = before.caller.sender ∧ after.caller.thisAddress = before.caller.thisAddress ∧
  after.caller.txOrigin = before.caller.txOrigin ∧ after.caller.msgValue = before.caller.msgValue ∧
  after.caller.selfBalance = before.caller.selfBalance ∧ after.caller.blockTimestamp = before.caller.blockTimestamp ∧
  after.caller.blockNumber = before.caller.blockNumber ∧ after.caller.chainId = before.caller.chainId ∧
  after.caller.blobBaseFee = before.caller.blobBaseFee ∧ after.caller.calldataSize = before.caller.calldataSize ∧
  after.caller.calldata = before.caller.calldata ∧
  (∀ slot, slot ≠ balanceSlot.slot → after.caller.knownAddresses slot = before.caller.knownAddresses slot)

def TraceRequestCorrect (before after : State) : Effect → Prop
  | .subscription id r _ => r = before.requests id ∧ r.requestType = .subscription ∧
      (after.requests id).requestStatus = .processed
  | .redemption id r _ _ _ => r = before.requests id ∧ r.requestType = .redemption ∧
      (after.requests id).requestStatus = .processed
  | .rejection id r => r = before.requests id ∧ (after.requests id).requestStatus = .rejected
  | _ => True

def AllowanceAccounting (before after : State) : Prop :=
  ∀ token owner spender, (before.config.assets token).asset = token → token ≠ 0 →
    let debits := (after.trace.map fun e => match e with
      | .redemption _ r _ _ payout =>
        if token = r.asset ∧ owner = before.config.portfolioSafe ∧ spender = before.config.self then payout else 0
      | _ => 0).sum
    if assetAllowance before token owner spender = wordLimit - 1 then
      assetAllowance after token owner spender = wordLimit - 1
    else (assetAllowance after token owner spender : Int) - assetAllowance before token owner spender = -(debits : Int)

def SettlementAccounting (env : Environment) (before after : State) (n : Nat)
    (approved rejected : List Nat) (asset : Address) (price : Nat) : Prop :=
  actualDecisions after.trace = expectedDecisions before env.now asset approved rejected ∧
  FeeCorrect env before after asset price ∧ CallerFrame before after asset ∧
  actualPayments after.trace = expectedPayments before.config after.trace ∧
  Balanced before after ∧ AllowanceAccounting before after ∧ RecordsConsistent after n ∧
  (consumed after.trace).Nodup ∧
  (∀ id, id ∈ consumed after.trace → id ∈ approved ∨ id ∈ rejected) ∧
  (∀ e, e ∈ after.trace → ConversionCorrect before.config price e ∧ TraceRequestCorrect before after e) ∧
  (∀ id, Payload (before.requests id) (after.requests id)) ∧
  (∀ id, (before.requests id).requestStatus ≠ .pending →
    (after.requests id).requestStatus = (before.requests id).requestStatus) ∧
  (∀ id, id ∈ consumed after.trace →
    (after.requests id).requestStatus = .processed ∨ (after.requests id).requestStatus = .rejected) ∧
  (∀ id, id ∉ consumed after.trace → after.requests id = before.requests id) ∧
  after.config = before.config ∧ after.lastSettledPrice asset = price

end Benchmark.Cases.KPK.SharesSettlementAccounting
