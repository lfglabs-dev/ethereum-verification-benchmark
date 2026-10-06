import Benchmark.Cases.KPK.SharesSettlementAccounting.Proofs

namespace Benchmark.Cases.KPK.SharesSettlementAccounting
open Verity
set_option maxHeartbeats 2000000

-- These are EXECUTABLE regressions, not universal accounting proofs.
def fixtureEnv : Environment :=
  {sender := 4, now := 100, hasCode := fun t => t == 9 || t == 10 || t == 11,
   isToken := fun t => t == 9 || t == 10,
   tokenAccepts := fun _ => true,
   feeResponder := fun args old => .ok (old 0 + args.rate,
     fun k => if k = 0 then old 0 + args.price else old k)}
def fixtureRequest (id : Nat) (investor receiver : Address) : UserRequest :=
  if id == 0 || id > 6 then default else
  {requestType := if id == 2 || id == 4 then .redemption else .subscription,
   requestStatus := if id == 6 then .processed else .pending,
   asset := if id == 5 then 10 else 9,
   assetAmount := if id == 2 || id == 4 then 8 * wad else 10 * wad,
   sharesAmount := if id == 2 || id == 4 then 10 * wad else 9 * wad,
   investor := investor, receiver := receiver, timestamp := 1,
   expiryAt := if id == 3 || id == 4 then 99 else 100}
def fixture (safe fee investor receiver : Address) : State :=
  {caller := ((do
      setStorage supplySlot (word (100 * wad))
      setMapping balanceSlot 1 (word (100 * wad))) defaultState).snd,
   external := {accountState := fun t k =>
      if t == 9 || t == 10 then
        if k == bslot 1 then 100 * wad
        else if k == bslot safe then 1000 * wad
        else if k == aslot safe 1 then 1000 * wad else 0
      else 0},
   config := {
     self := 1, portfolioSafe := safe, feeReceiver := fee,
     performanceFeeModule := 11, managementFeeRate := 0, redemptionFeeRate := 1000,
     performanceFeeRate := 0,
     assets := fun t => if t == 9 || t == 10 then
       {asset := t, decimals := 18, canDeposit := true, canRedeem := true, isFeeModuleAsset := true}
       else default,
     operators := fun a => a == 4},
   requests := fun id => fixtureRequest id investor receiver,
   subscriptionAssets := fun t => if t == 9 then 20 * wad else if t == 10 then 10 * wad else 0,
   pendingRequestsCount := fun t => if t == 9 then 4 else if t == 10 then 1 else 0,
   managementFeeLastUpdate := 0, performanceFeeLastUpdate := 0,
   lastSettledPrice := fun _ => 0}

def runFixture (s : State) (approved rejected : List Nat) (env : Environment := fixtureEnv)
    (price : Nat := usd) : Except String (Unit × State) :=
  processRequests env approved rejected 9 price s

def decisionPairs (trace : List Effect) : List (Nat × Nat) :=
  (actualDecisions trace).map fun d => (d.id, if d.status == .processed then 1 else 2)

def checkRun (s : State) (approved rejected : List Nat) : Bool :=
  match runFixture s approved rejected with
  | .error _ => false
  | .ok (_, next) =>
    let ps := expectedPayments s.config next.trace
    let xs : List Address := [1,2,3,4]
    actualPayments next.trace == ps &&
    decisionPairs next.trace == ((expectedDecisions s fixtureEnv.now 9 approved rejected).map fun d =>
      (d.id, if d.status == .processed then 1 else 2)) &&
    (decide ((consumed next.trace).Nodup)) &&
    ((totalSupply next : Int) - totalSupply s == (ps.map supplyEffect).sum) &&
    xs.all (fun x => (shareBalance next x : Int) - shareBalance s x == (ps.map (shareEffect x)).sum) &&
    xs.all (fun x => (assetBalance next 9 x : Int) - assetBalance s 9 x == (ps.map (assetEffect 9 x)).sum) &&
    (List.range 7).all (fun id => decide ((s.requests id).requestType = (next.requests id).requestType ∧
      (s.requests id).assetAmount = (next.requests id).assetAmount ∧
      (s.requests id).sharesAmount = (next.requests id).sharesAmount ∧
      (s.requests id).investor = (next.requests id).investor ∧
      (s.requests id).receiver = (next.requests id).receiver ∧
      (s.requests id).expiryAt = (next.requests id).expiryAt)) &&
    next.subscriptionAssets 9 == SubLiability next 7 9 &&
    next.pendingRequestsCount 9 == PendingCount next 7 9 && next.lastSettledPrice 9 == usd

-- Independently chosen branches/aliases are checked against Specs, not fixture
-- oracle quote/fee stubs. Both actual production two-stage converters execute.
def arrays : List (List Nat) :=
  [[]] ++ (List.range 6).map (fun i => [i]) ++
  (List.range 6).flatMap (fun i => (List.range 6).map (fun j => [i,j]))

def regression : Bool := arrays.all fun a => arrays.all fun r => checkRun (fixture 2 4 3 3) a r

def aliases : Bool := [1,2,3,4].all fun v => [1,2,3,4].all fun f =>
  [1,2,3,4].all fun i => [1,2,3,4].all fun r =>
    checkRun (fixture v f i r) [1,2,3,4,1,2,6,5,0] [2,1,3,4,5,0]

-- Full 128-record traversal, using production conversion/transfer code.
def longFixture : State :=
  let base := fixture 2 4 3 3
  {base with
    requests := (fun id => if id > 0 && id <= 128 then fixtureRequest 1 3 3 else (default : UserRequest)),
    subscriptionAssets := fun a => if a == 9 then 1280 * wad else 0,
    pendingRequestsCount := fun a => if a == 9 then 128 else 0,
    external := writeExternal base.external 9 (bslot 1) (1280 * wad)}
def longRun : Bool :=
  match runFixture longFixture ((List.range 128).map (· + 1)) [] with
  | .error _ => false
  | .ok (_, s) => (consumed s.trace).length == 128 && totalSupply s == 1380 * wad &&
    assetBalance s 9 1 == 0 && s.pendingRequestsCount 9 == 0

def isFailure (r : Except String (Unit × State)) : Bool :=
  match r with | .error _ => true | _ => false

def failures : Bool :=
  let base := fixture 2 4 3 3
  isFailure (runFixture base [1] [] {fixtureEnv with sender := 3}) &&
  isFailure (runFixture base [1] [] fixtureEnv 0) &&
  isFailure (runFixture base [1] [] {fixtureEnv with tokenAccepts := fun _ => false}) &&
  isFailure (runFixture {base with external := writeExternal base.external 9 (aslot 2 1) 0} [1,2] []) &&
  isFailure (runFixture {base with requests := fun id =>
    if id == 2 then {base.requests id with assetAmount := 1000 * wad} else base.requests id} [1,2] [])

def feeFixture : State :=
  let base := fixture 2 4 3 3
  {base with config := {base.config with managementFeeRate := 1000, performanceFeeRate := 100}}

def fees : Bool :=
  let env := {fixtureEnv with now := 31536000}
  match runFixture feeFixture [] [] env with
  | .error _ => false
  | .ok (_, s) => totalSupply s == 110 * wad + 100 && shareBalance s 4 == 10 * wad + 100 &&
    s.managementFeeLastUpdate == env.now && s.performanceFeeLastUpdate == env.now &&
    s.external.accountState 11 0 == usd &&
    (actualPayments s.trace == expectedPayments feeFixture.config s.trace)

-- Late failure: whole persistent caller/token/module snapshot is returned by
-- transaction; rollback theorem is kernel-checked, this check exercises the path.
def lateRollback : Bool :=
  let base := feeFixture
  let s := {base with requests := fun id =>
    if id == 2 then {base.requests id with expiryAt := 2^64-1, assetAmount := 1000 * wad}
    else if id == 1 then {base.requests id with expiryAt := 2^64-1} else base.requests id}
  let env := {fixtureEnv with now := 31536000}
  let result := transaction (processRequests env [1,2] [] 9 usd) s
  isFailure result.1 && totalSupply result.2 == totalSupply s &&
    result.2.external.accountState 11 0 == s.external.accountState 11 0 &&
    assetBalance result.2 9 1 == assetBalance s 9 1 && result.2.managementFeeLastUpdate == 0

#eval ("array-pairs", arrays.length * arrays.length, regression)
#eval ("role-aliases", 256, aliases)
#eval ("128-record-traversal", longRun)
#eval ("failure-paths", failures)
#eval ("fee-prefix", fees)
#eval ("late-whole-world-rollback", lateRollback)
def quote (s : State) (c : Tx Nat) : Option Nat :=
  match c s with | .error _ => none | .ok (n, _) => some n

def edgeArithmetic : Bool :=
  let base := fixture 2 4 3 3
  let disabled := {base with config := {base.config with assets := fun _ => default}}
  let dec36 := {base with config := {base.config with assets := fun a => {base.config.assets a with decimals := 36}}}
  quote disabled (assetsToShares 1 0 9) == some 0 &&
  quote disabled (assetsToShares 0 1 9) == some 0 &&
  quote disabled (sharesToAssets 1 0 9) == some 0 &&
  quote disabled (sharesToAssets 0 1 9) == some 0 &&
  quote disabled (assetsToShares 1 1 9) == none &&
  quote disabled (sharesToAssets 1 1 9) == none &&
  -- First-stage overflow even when the eventual single rational quotient fits.
  quote dec36 (assetsToShares (wordLimit-1) usd 9) == none &&
  -- Ordinary checked price*WAD overflow precedes full-precision mulDiv.
  quote base (sharesToAssets 1 (wordLimit-1) 9) == none &&
  quote base (assetsToShares (10*wad+123) usd 9) == some (10*wad+123) &&
  quote base (sharesToAssets (10*wad+123) usd 9) == some (10*wad+123)

def infiniteAllowance : Bool :=
  let base := fixture 2 4 3 3
  let s := {base with external := writeExternal base.external 9 (aslot 2 1) (wordLimit-1)}
  match runFixture s [2] [] with
  | .error _ => false
  | .ok (_, next) => assetAllowance next 9 2 1 == wordLimit-1

#eval ("arithmetic-edge-paths", edgeArithmetic)
#eval ("infinite-allowance", infiniteAllowance)

-- Enforce test failure as a failed build, not merely a printed false value.
#eval (do
  if !(regression && aliases && longRun && failures && fees && lateRollback && edgeArithmetic && infiniteAllowance) then
    throw (IO.userError "KPK regression failure") : IO Unit)
def checkFeeFinite (env : Environment) (before after : State) (asset : Address) (price : Nat) : Bool :=
  match expectedFeePrefix env before asset price with
  | .error _ => false
  | .ok receipt =>
    let suffix := after.trace.drop receipt.trace.length
    let world := suffix.foldl (expectedWorldStep before.config) receipt.world
    after.trace.take receipt.trace.length == receipt.trace &&
    suffix.all (fun e => !isFeeMarker e) &&
    after.managementFeeLastUpdate == receipt.managementTime &&
    after.performanceFeeLastUpdate == receipt.performanceTime &&
    ([9,10,11,12] : List Nat).all (fun target =>
      ([0,7,101] ++ ([1,2,3,4] : List Address).map bslot ++
        ([1,2,3,4] : List Address).flatMap (fun a => ([1,2,3,4] : List Address).map (aslot a))).all
        (fun slot => after.external.accountState target slot == world.accountState target slot))

def feeMutationControls : Bool :=
  let base := fixture 2 4 3 3
  let bogus := {base with trace := [.mint 4 7,.performance 7]}
  let nowEnv := {fixtureEnv with now := 31536000}
  let noCode := {nowEnv with hasCode := fun t => t != 11 && fixtureEnv.hasCode t}
  let disabled := {feeFixture with config := {feeFixture.config with performanceFeeModule := 0}}
  let boundaryEnv := {fixtureEnv with now := 21600}
  (!checkFeeFinite fixtureEnv base bogus 9 usd) &&
  (isFailure (runFixture feeFixture [] [] noCode)) &&
  (match runFixture disabled [] [] nowEnv with
    | .error _ => false | .ok (_, next) => checkFeeFinite nowEnv disabled next 9 usd && feeSum false next.trace == 0) &&
  (match runFixture feeFixture [] [] boundaryEnv with
    | .error _ => false | .ok (_, next) => checkFeeFinite boundaryEnv feeFixture next 9 usd && next.trace.isEmpty) &&
  (match runFixture feeFixture [] [] nowEnv with
    | .error _ => false
    | .ok (_, next) =>
      let missingCall := {next with trace := next.trace.filter (fun e => match e with | .moduleCall _ _ _ _ _ _ => false | _ => true)}
      let wrongWorld := {next with external := writeExternal next.external 11 7 999}
      checkFeeFinite nowEnv feeFixture next 9 usd &&
      !checkFeeFinite nowEnv feeFixture missingCall 9 usd &&
      !checkFeeFinite nowEnv feeFixture wrongWorld 9 usd)

-- M4: preserve actual unchecked OZ credit on the admitted incoherent word world.
-- Such a world fails the newly explicit coherent-token applicability premise.
def tokenWrapControl : Bool :=
  let base := fixture 2 4 3 3
  let s := {base with external := writeExternal (writeExternal base.external 9 (bslot 1) 1) 9 (bslot 2) (wordLimit-1)}
  match safeTransfer fixtureEnv 9 1 2 1 s with
  | .error _ => false
  | .ok (_, next) => assetBalance next 9 2 == 0 && assetBalance next 9 1 == 0

#eval ("fee-spec-mutation-controls", feeMutationControls)
#eval ("unchecked-token-credit-control", tokenWrapControl)
#eval (do
  if !(feeMutationControls && tokenWrapControl) then throw (IO.userError "KPK revision regression failure") : IO Unit)
def checkSpecFinite (before after : State) (approved rejected : List Nat) : Bool :=
  let cfg := before.config
  let xs : List Address := [0,1,2,3,4]
  checkFeeFinite fixtureEnv before after 9 usd &&
  after.trace.all (fun e => match e with
    | .subscription id r m =>
      r == before.requests id && r.requestType == .subscription &&
      (after.requests id).requestStatus == .processed &&
      m == Mint r.assetAmount usd (cfg.assets r.asset).decimals && m >= r.sharesAmount &&
      m*usd*10^(cfg.assets r.asset).decimals <= r.assetAmount*wad*usd &&
      r.assetAmount*wad*usd < (m+1)*usd*10^(cfg.assets r.asset).decimals
    | .redemption id r fee net payout =>
      r == before.requests id && r.requestType == .redemption &&
      (after.requests id).requestStatus == .processed &&
      fee == RedeemFee r.sharesAmount cfg.redemptionFeeRate && net == r.sharesAmount-fee &&
      payout == Out net usd (cfg.assets r.asset).decimals && payout >= r.assetAmount &&
      payout*wad*usd <= net*usd*10^(cfg.assets r.asset).decimals &&
      net*usd*10^(cfg.assets r.asset).decimals < (payout+1)*wad*usd
    | .rejection id r => r == before.requests id && (after.requests id).requestStatus == .rejected
    | _ => true) &&
  xs.all (fun a => if a == 9 then true else after.lastSettledPrice a == before.lastSettledPrice a) &&
  xs.all (fun a => xs.all (fun b =>
    after.caller.readMap2 allowanceSlot.slot a b == before.caller.readMap2 allowanceSlot.slot a b)) &&
  xs.all (fun a => xs.all (fun b =>
    let debits := (after.trace.map fun e => match e with
      | .redemption _ r _ _ payout => if r.asset == 9 && a == cfg.portfolioSafe && b == cfg.self then payout else 0
      | _ => 0).sum
    if assetAllowance before 9 a b == wordLimit-1 then assetAllowance after 9 a b == wordLimit-1
    else (assetAllowance after 9 a b : Int)-assetAllowance before 9 a b == -(debits : Int))) &&
  (consumed after.trace).all (fun id => (approved ++ rejected).contains id)

def expandedRegressions : Bool := arrays.all fun a => arrays.all fun r =>
  let before := fixture 2 4 3 3
  match runFixture before a r with
  | .error _ => false | .ok (_, after) => checkSpecFinite before after a r

def expandedAliases : Bool := [1,2,3,4].all fun v => [1,2,3,4].all fun f =>
  [1,2,3,4].all fun i => [1,2,3,4].all fun r =>
    let before := fixture v f i r
    let approved := [1,2,3,4,1,2,6,5,0]
    let rejected := [2,1,3,4,5,0]
    match runFixture before approved rejected with
    | .error _ => false | .ok (_, after) => checkSpecFinite before after approved rejected

#eval ("expanded-spec-array-pairs", expandedRegressions)
#eval ("expanded-spec-role-aliases", expandedAliases)
#eval (do
  if !(expandedRegressions && expandedAliases) then throw (IO.userError "KPK expanded spec regression failure") : IO Unit)
end Benchmark.Cases.KPK.SharesSettlementAccounting
