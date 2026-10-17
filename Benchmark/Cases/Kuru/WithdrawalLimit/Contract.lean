/-
Kuru V2 AccountCore payout/transaction semantic model.
Pinned provenance and reproduction instructions are in case.yaml and README.md.

Simplifications and boundaries (not undisclosed axioms):
1. The limiter's executable code is in Limiter/History. Core uses Verity addresses,
   explicit persistent/transient records and integer projections of word fields.
   Proxy-owned guard storage is separate from limiter transient storage. Guard
   enter compares the actual address sentinel; exit stores implementation codesize.
2. SignatureChecker/EIP712 is an external static acceptance interface bound to the
   exact payload, root owner, chain id, proxy address, name/version/type. `accepted`
   means EOA/ERC1271 acceptance, not human assent or a cryptography theorem.
3. ERC20 transfer results and BEFORE/AFTER balanceOf observations are supplied by
   the environment and checked exactly as source. Truthfulness, recipients' token
   balances, ERC20 internals and prices' economic correctness are NOT proven.
4. Every callback is a finite list of attempted unguarded policy/environment
   operations (with catch/propagate choice) or an attempted guarded entry. Native
   refunds call receive and create surplus, never deposit credit. No blanket ban
   on callbacks. All policy checks are observations at their original checkpoint.
5. Exchange/account-grant operations not reproduced instruction-by-instruction
   are an explicit overapproximate `InternalFrame`: balance/reserve/grant and
   Core Ownable-owner changes may be arbitrary in-range, but may NOT write limiter, nonce,
   authority, epoch, freeze, time or physical custody. This is a manual source
   writer-frame boundary, NOT proof of whole-exchange arithmetic or authorization.
   All ordinary permission checks still read actual modeled account/grant records.
   Root registration uses the actual `ensureRoot` helper; existing root-account
   metadata/owners cannot be replaced by a frame. Child allocation uses the concrete
   bounded shared-ID/list writer below; creation authorization/signature remains
   excluded via a successful-helper projection, not omitted writes. Guarded
   excluded calls select pause/guard modifiers independently and enter/exit or
   roll back, including root allocation in the same atomic frame. Unknown external
   writers cannot mutate stable fields through this frame.
6. External governance-registry and price-provider mutations are unrestricted
   environmental actions; contract-view answers themselves do not mutate state.
   Source configuration/code-presence checks are concrete. Built-in price-source
   implementations and external role-registry authorization are outside scope.
7. Rejection discards tentative persistent, transient, custody and callback writes.
   Caught failures keep earlier calls; uncaught route failure restores its entry.
   The timestamp stays fixed within a route. New transactions clear transients,
   accept only monotone timestamps, and preserve every persistent funding field.
8. Logs use measured ERC20 custody debit and gross native payout. No claim of net
   native debit, recipient receipt economics,
   net-inflow/loss bound, deployment/upgrade safety or bytecode refinement. No
   upgrade transition exists: the trace is for unchanged pinned implementations.
9. This is a Verity-type/rely-guarantee semantic model, not emitted Yul. Compile
   checks all executable definitions/specifications; it must not be described as
   a Solidity-to-Verity compiler proof. DSL integration is not yet implemented.
-/
import Benchmark.Cases.Kuru.WithdrawalLimit.Contract.Limiter

namespace Benchmark.Cases.Kuru.WithdrawalLimit

structure Roles where
  governance : Key := 0
  ops : Key := 0
  emergency : Key := 0

structure AccountMeta where
  owner : Key := 0
  rootId : Nat := 0
  subaccountSeq : Nat := 0
  deriving DecidableEq

structure SignerAuth where
  permissions : Nat := 0
  expiry : Nat := 0
  deriving DecidableEq

structure TokenConfig where
  decimals : Nat := 0
  enabled : Bool := false
  seen : Bool := false

/-- Solady persistent slot owned by the executing Core PROXY, not the limiter. -/
def coreGuardSlot : Nat := 0x929eee149b4bd21268

structure Core where
  owner : Key := 0
  feeCollector : Key := 0
  registry : Key := 0
  paused : Bool := false
  guardWord : Nat := 0
  limiterBound : Bool := false
  authority : Key := 0
  epoch : Nat := 0
  frozen : Bool := false
  tokenFrozen : Key → Bool := fun _ => false
  approvedNonces : Key → Nat := fun _ => 0
  lastAccountId : Nat := 0
  rootAccountIdOf : Key → Nat := fun _ => 0
  accounts : Nat → AccountMeta := fun _ => {}
  /-- Ordered IDs matching _subaccountsByRoot; no deletion writer exists. -/
  subaccountsByRoot : Nat → List Nat := fun _ => []
  grants : Nat → Key → SignerAuth := fun _ _ => {}
  balances : Nat → Key → Nat := fun _ _ => 0
  reserves : Nat → Key → Nat := fun _ _ => 0
  tokens : Key → TokenConfig := fun _ => {}

structure Deployment where
  coreAddress : Key
  limiterAddress : Key
  limiterImmutableCore : Key
  coreImplementationCodeSize : Nat
  chainId : Nat
  codePresent : Key → Bool

structure ApprovedWithdrawal where
  account : Key
  token : Key
  recipient : Key
  amount : Nat
  nonce : Nat
  deadline : Nat
  authorityEpoch : Nat
  deriving DecidableEq

structure SignatureAcceptance where
  owner : Key
  domainProxy : Key
  chainId : Nat
  name : String := "KuruAccountCore"
  version : String := "1"
  typeString : String := "ApprovedWithdrawal(address account,address token,address recipient,uint256 amount,uint256 nonce,uint256 deadline,uint64 authorityEpoch)"
  payload : ApprovedWithdrawal
  accepted : Bool

inductive PayoutKind where | ordinary | approved deriving DecidableEq

structure Payout where
  kind : PayoutKind
  token : Key
  recipient : Key
  /-- Actual observed ERC20 custody debit, or requested native gross payout. -/
  amount : Nat
  /-- Ordinary valued actual debit; approved amount deliberately NOT valued. -/
  funding : Option Funding
  approvedInstruction : Option ApprovedWithdrawal

structure World where
  now : Nat
  core : Core
  limiter : Limiter
  roles : Key → Roles := fun _ => {}
  quotes : PriceFetch := fun _ => .error .price
  nativeCustody : Nat := 0
  payouts : List Payout := []

def update {α : Type} (f : Key → α) (k : Key) (v : α) : Key → α :=
  fun x => if x = k then v else f x

def updateBalance (f : Nat → Key → Nat) (id : Nat) (token : Key) (v : Nat) : Nat → Key → Nat :=
  fun i k => if i = id ∧ k = token then v else f i k

def requireRoot (c : Core) (id : Nat) : Checked Unit := do
  ensure ((c.accounts id).rootId ≠ 0) .account
  ensure ((c.accounts id).rootId = id) .account

/-- _registerAccount: checked shared uint40 allocator for ROOT and CHILD records. -/
def registerAccount (c : Core) (owner : Key) (rootId sequence : Nat) : Checked (Nat × Core) := do
  let next ← checkedAdd 40 c.lastAccountId 1
  let root := if rootId = 0 then next else rootId
  return (next, { c with
    lastAccountId := next
    accounts := fun i => if i = next then ⟨owner, root, sequence⟩ else c.accounts i })

def ensureRoot (c : Core) (owner : Key) : Checked (Nat × Core) := do
  ensure (owner ≠ 0) .account
  let id := c.rootAccountIdOf owner
  if id ≠ 0 then return (id, c)
  let (next, c) ← registerAccount c owner 0 0
  return (next, { c with rootAccountIdOf := update c.rootAccountIdOf owner next })

/-- _createSubaccount's retained-state effects; caller already established ROOT.
    Both public creation paths' authorization/signature checks remain excluded. -/
def createSubaccount (c : Core) (rootId : Nat) : Checked (Nat × Core) := do
  requireRoot c rootId
  let children := c.subaccountsByRoot rootId
  let sequence := children.length + 1
  ensure (sequence ≤ maxWord 16) .account
  let (id, c) ← registerAccount c (c.accounts rootId).owner rootId sequence
  return (id, { c with subaccountsByRoot := fun i =>
    if i = rootId then children ++ [id] else c.subaccountsByRoot i })

/-- Exact WITHDRAW permission path for root calls, inclusive signer expiry. -/
def withdrawAuthorized (c : Core) (now id : Nat) (caller : Key) : Bool :=
  let accountMeta := c.accounts id
  if accountMeta.rootId = 0 then false
  else if caller = accountMeta.owner then true
  else
    let auth := c.grants accountMeta.rootId caller
    if auth.expiry ≠ 0 ∧ now > auth.expiry then false
    else decide (Nat.testBit auth.permissions 4 = true ∨ Nat.testBit auth.permissions 3 = true)

def requireGovernance (w : World) (caller : Key) : Checked Unit := do
  ensure (w.core.registry ≠ 0) .config
  ensure (caller = (w.roles w.core.registry).governance) .unauthorized

def requireGovEmergency (w : World) (caller : Key) : Checked Unit := do
  ensure (w.core.registry ≠ 0) .config
  let r := w.roles w.core.registry
  ensure (caller = r.governance ∨ caller = r.emergency) .unauthorized

def requireRelease (c : Core) (token : Key) : Checked Unit := do
  ensure (c.frozen = false ∧ c.tokenFrozen token = false) .frozen

def requireLimiter (w : World) : Checked Unit := ensure (w.core.limiterBound = true) .binding

/-- Persistent source Solady guard, NOT DSL transient `nonreentrant`. -/
def guardEnter (d : Deployment) (w : World) : Checked World := do
  ensure (w.core.guardWord ≠ d.coreAddress.toNat) .reentrant
  return { w with core := { w.core with guardWord := d.coreAddress.toNat } }

/-- Source protocolActive is independent of the persistent nonReentrant modifier. -/
def activeGuardEnter (d : Deployment) (w : World) : Checked World := do
  ensure (w.core.paused = false) .paused
  guardEnter d w

def guardExit (d : Deployment) (w : World) : World :=
  { w with core := { w.core with guardWord := d.coreImplementationCodeSize } }

/-- Explicit source-writer overapproximation; it cannot manufacture payouts. -/
structure InternalFrame where
  /-- Core Ownable owner can change; existing ROOT ACCOUNT owners cannot. -/
  owner : Key
  grants : Nat → Key → SignerAuth
  balances : Nat → Key → Nat
  reserves : Nat → Key → Nat
  /-- Select each source modifier independently; guard-only calls work paused. -/
  guarded : Bool := false
  protocolActive : Bool := false
  /-- Optional retained root registration in the SAME atomic source-operation frame. -/
  registerRoot : Option Key := none

/-- Not a callable Solidity method. This is the named excluded exchange boundary. -/
def applyInternalFrame (w : World) (f : InternalFrame) : World :=
  { w with core := { w.core with
    owner := f.owner
    grants := f.grants
    balances := f.balances
    reserves := f.reserves } }

inductive PolicyAction where
  | setRegistry (registry : Key)
  | setFeeCollector (owner : Key)
  | pause (paused : Bool)
  | rotateAuthority (authority : Key)
  | freeze (frozen : Bool)
  | freezeToken (token : Key) (frozen : Bool)
  | invalidateNonce (account : Key) (next : Nat)
  | bindLimiter (limiter : Key)
  | configureDrip (capacity rate : Nat)
  | configureSource (token source : Key)
  | configureToken (token : Key) (enabled : Bool) (metadata : Checked Nat)
  | receiveNative (amount : Nat)
  | nestedGuarded
  | observe

/-- Concrete unguarded policy writers; failures can be caught by a callback. -/
def policyAction (d : Deployment) (w : World) (caller : Key) : PolicyAction → Checked World
  | .setFeeCollector owner => do
    requireGovernance w caller
    let (_, core) ← ensureRoot w.core owner
    return { w with core := { core with feeCollector := owner } }
  | .setRegistry registry => do
    ensure (caller = w.core.owner) .unauthorized
    ensure (registry ≠ 0) .config
    let r := w.roles registry
    ensure (r.governance ≠ 0 ∧ r.ops ≠ 0 ∧ r.emergency ≠ 0) .config
    return { w with core := { w.core with registry := registry } }
  | .pause paused => do
    if paused then requireGovEmergency w caller else do
      ensure (w.core.registry ≠ 0) .config
      let r := w.roles w.core.registry
      ensure (caller = r.governance ∨ caller = r.ops) .unauthorized
    return { w with core := { w.core with paused := paused } }
  | .rotateAuthority authority => do
    requireGovernance w caller
    let epoch ← checkedAdd 64 w.core.epoch 1
    return { w with core := { w.core with authority := authority, epoch := epoch } }
  | .freeze frozen => do
    if frozen then requireGovEmergency w caller else requireGovernance w caller
    return { w with core := { w.core with frozen := frozen } }
  | .freezeToken token frozen => do
    if frozen then requireGovEmergency w caller else requireGovernance w caller
    return { w with core := { w.core with tokenFrozen := update w.core.tokenFrozen token frozen } }
  | .invalidateNonce account next => do
    ensure (next < width 256) .nonce
    let id := w.core.rootAccountIdOf account
    requireRoot w.core id
    ensure (caller = (w.core.accounts id).owner) .unauthorized
    ensure (next > w.core.approvedNonces account) .nonce
    return { w with core := { w.core with approvedNonces := update w.core.approvedNonces account next } }
  | .bindLimiter limiter => do
    requireGovernance w caller
    ensure (w.core.limiterBound = false) .binding
    ensure (limiter = d.limiterAddress ∧ d.codePresent limiter = true) .config
    ensure (d.limiterImmutableCore = d.coreAddress) .config
    return { w with core := { w.core with limiterBound := true } }
  | .configureDrip capacity rate => do
    -- Limiter consults current Core registry. Core pause/freeze is NOT a gate here.
    let l ← setDripConfig w.limiter w.now caller (w.roles w.core.registry).governance capacity rate
    return { w with limiter := l }
  | .configureSource token source => do
    let l ← setPriceSource w.limiter caller (w.roles w.core.registry).governance token source d.codePresent
    return { w with limiter := l }
  | .configureToken token enabled metadata => do
    requireGovernance w caller
    let old := w.core.tokens token
    let config ← if enabled then do
      let dec ← if token = 0 then pure 18 else metadata
      ensure (dec ≤ 77) .config
      if old.seen then ensure (old.decimals = dec) .config
      requireLimiter w
      let _ ← price w.limiter w.quotes token
      pure (TokenConfig.mk dec true true)
      else pure (TokenConfig.mk old.decimals false old.seen)
    return { w with core := { w.core with tokens := update w.core.tokens token config } }
  | .receiveNative amount => do
    let n ← checkedAdd 256 w.nativeCustody amount
    return { w with nativeCustody := n }
  | .nestedGuarded => do
    let _ ← activeGuardEnter d w
    -- Successful non-reentrant calls are modeled by deposit/withdraw/approved,
    -- not by this attempt marker. During a payout this MUST reject at the guard.
    return w
  | .observe => .ok w

/-- External publication is not a limiter writer and cannot invalidate a cache. -/
inductive EnvironmentAction where
  | publish (source : Key) (quote : Checked Nat)
  | registryResponse (registry : Key) (roles : Roles)
  | internalFrame (frame : InternalFrame)
  /-- Source helper projection for non-custody root-account registration. -/
  | ensureRootAccount (owner : Key)
  /-- Successful helper projection from either public child-creation path.
      Overapproximates authorization, NOT allocation/list/guard behavior. -/
  | createChild (rootOwner : Key)

/-- These environment actions are explicit applicability boundaries, not public APIs. -/
def environmentAction (d : Deployment) (w : World) : EnvironmentAction → World
  | .publish source quote => { w with quotes := update w.quotes source quote }
  | .registryResponse registry roles => { w with roles := update w.roles registry roles }
  | .internalFrame frame =>
    match (do
      if frame.protocolActive then ensure (w.core.paused = false) .paused
      let entered ← if frame.guarded then guardEnter d w else pure w
      let registered ← match frame.registerRoot with
        | none => pure entered
        | some owner => do
          let (_, core) ← ensureRoot entered.core owner
          pure { entered with core := core }
      let next := applyInternalFrame registered frame
      pure (if frame.guarded then guardExit d next else next) : Checked World) with
    | .ok next => next
    | .error _ => w
  | .ensureRootAccount owner =>
    match ensureRoot w.core owner with
    | .ok (_, core) => { w with core := core }
    | .error _ => w
  | .createChild owner =>
    match (do
      let entered ← activeGuardEnter d w
      let (root, core) ← ensureRoot entered.core owner
      let (_, core) ← createSubaccount core root
      pure (guardExit d { entered with core := core }) : Checked World) with
    | .ok next => next
    | .error _ => w

/-- Source-facing view: decimals come from Core, never from the caller. -/
def previewCoreWithdrawal (w : World) (token : Key) (amount : Nat) : Checked (Nat × Nat × Bool) :=
  previewWithdrawal w.limiter w.now w.quotes token amount (w.core.tokens token).decimals

structure Callback where
  caller : Key
  action : PolicyAction
  catchFailure : Bool := true
  environmentBefore : List EnvironmentAction := []

/-- Ordered callbacks execute at the external interaction checkpoint. -/
def callbacks (d : Deployment) : List Callback → World → Checked World
  | [], w => .ok w
  | c :: cs, w =>
    let observed := c.environmentBefore.foldl (environmentAction d) w
    match policyAction d observed c.caller c.action with
    | .ok next => callbacks d cs next
    | .error e => if c.catchFailure then callbacks d cs observed else .error e

structure TransferObservation where
  callSucceeds : Bool := true
  readsSucceed : Bool := true
  beforeBalance : Nat := 0
  afterBalance : Nat := 0
  callbacks : List Callback := []

/-- The only modeled physical-outflow helper; two direct Core callers below. -/
def transferAsset (d : Deployment) (w : World) (token recipient : Key)
    (amount : Nat) (obs : TransferObservation) : Checked (Nat × World) := do
  if token = 0 then
    ensure (w.nativeCustody ≥ amount) .transfer
    let w := { w with nativeCustody := w.nativeCustody - amount }
    let w ← callbacks d obs.callbacks w
    ensure (obs.callSucceeds = true) .transfer
    return (amount, w)
  else
    ensure (obs.readsSucceed = true ∧ obs.beforeBalance < width 256) .transfer
    let w ← callbacks d obs.callbacks w
    ensure (obs.callSucceeds = true) .transfer
    ensure (obs.afterBalance < width 256) .transfer
    ensure (obs.afterBalance < obs.beforeBalance ∧ obs.beforeBalance - obs.afterBalance ≤ amount) .transfer
    -- Recipient proceeds are not inferred from these observations.
    let _ := recipient
    return (obs.beforeBalance - obs.afterBalance, w)

/-- Source _withdrawAsset prefix: reserve the requested maximum, then pin flow/price.
    Factored at the external CALL, like approvedBeforeTransfer. -/
def withdrawBeforeTransfer (d : Deployment) (w : World) (id : Nat) (token : Key)
    (amount : Nat) : Checked World := do
  ensure (w.core.balances id token ≥ amount) .balance
  let w := { w with core := { w.core with balances := updateBalance w.core.balances id token (w.core.balances id token - amount) } }
  requireLimiter w
  let limiter ← checkApprovedWithdrawal w.limiter w.now w.quotes d.coreAddress d.coreAddress token
  return { w with limiter := limiter }

/-- Source _withdrawAsset suffix. Add to the POST-callback ledger, checked for overflow. -/
def refundAsset (w : World) (id : Nat) (token : Key) (amount debited : Nat) : Checked World := do
  if debited < amount then
    let balance ← checkedAdd 256 (w.core.balances id token) (amount - debited)
    return { w with core := { w.core with balances := updateBalance w.core.balances id token balance } }
  else return w

structure OrdinaryArgs where
  rootId : Nat
  token : Key
  amount : Nat
  recipient : Key

def withdraw (d : Deployment) (w : World) (caller : Key)
    (a : OrdinaryArgs) (obs : TransferObservation) : Checked World := do
  ensure (a.rootId < width 40 ∧ a.amount < width 256) .config
  let w ← activeGuardEnter d w
  requireRoot w.core a.rootId
  ensure (withdrawAuthorized w.core w.now a.rootId caller = true) .unauthorized
  ensure (a.amount > 0) .amount
  ensure (a.recipient ≠ 0 ∧ a.recipient ≠ d.coreAddress) .recipient
  requireRelease w.core a.token
  let prepared ← withdrawBeforeTransfer d w a.rootId a.token a.amount
  let (debited, transferred) ← transferAsset d prepared a.token a.recipient a.amount obs
  let w ← refundAsset transferred a.rootId a.token a.amount debited
  requireLimiter w
  let (funding, limiter) ← recordWithdrawal w.limiter w.now w.quotes d.coreAddress d.coreAddress
    a.token debited (w.core.tokens a.token).decimals
  return guardExit d { w with limiter := limiter, payouts := w.payouts ++ [⟨.ordinary, a.token, a.recipient,
    debited, some funding, none⟩] }

def signatureValid (d : Deployment) (owner : Key) (q : ApprovedWithdrawal)
    (sig : SignatureAcceptance) : Bool := decide (
  owner ≠ 0 ∧ sig.owner = owner ∧ sig.domainProxy = d.coreAddress ∧ sig.chainId = d.chainId ∧
  sig.name = "KuruAccountCore" ∧ sig.version = "1" ∧
  sig.typeString = "ApprovedWithdrawal(address account,address token,address recipient,uint256 amount,uint256 nonce,uint256 deadline,uint64 authorityEpoch)" ∧
  sig.payload = q ∧ sig.accepted = true)

/-- Model-only factor of Core:258-283, before the recipient/token CALL. -/
def approvedBeforeTransfer (d : Deployment) (w : World) (caller : Key)
    (q : ApprovedWithdrawal) (sig : SignatureAcceptance) : Checked World := do
  ensure (q.amount < width 256 ∧ q.nonce < width 256 ∧ q.deadline < width 256 ∧
    q.authorityEpoch < width 64) .config
  let w ← activeGuardEnter d w
  ensure (caller = w.core.authority ∧ caller ≠ 0) .unauthorized
  let id := w.core.rootAccountIdOf q.account
  requireRoot w.core id
  ensure (q.amount ≠ 0) .amount
  ensure (q.recipient ≠ 0 ∧ q.recipient ≠ d.coreAddress) .recipient
  ensure (w.now ≤ q.deadline) .deadline
  ensure (q.authorityEpoch = w.core.epoch) .signature
  ensure (q.nonce = w.core.approvedNonces q.account) .nonce
  ensure (signatureValid d (w.core.accounts id).owner q sig = true) .signature
  requireRelease w.core q.token
  let nextNonce ← checkedAdd 256 q.nonce 1
  let w := { w with core := { w.core with
    approvedNonces := update w.core.approvedNonces q.account nextNonce } }
  -- Inline withdrawBeforeTransfer at this model-only checkpoint to expose the
  -- source nonce-before-reservation order to checkpoint proofs.
  ensure (w.core.balances id q.token ≥ q.amount) .balance
  let w := { w with core := { w.core with
    balances := updateBalance w.core.balances id q.token (w.core.balances id q.token - q.amount) } }
  requireLimiter w
  let limiter ← checkApprovedWithdrawal w.limiter w.now w.quotes d.coreAddress d.coreAddress q.token
  return { w with limiter := limiter }

def fulfillApprovedWithdrawal (d : Deployment) (w : World) (caller : Key)
    (q : ApprovedWithdrawal) (sig : SignatureAcceptance) (obs : TransferObservation) : Checked World := do
  let prepared ← approvedBeforeTransfer d w caller q sig
  let (debited, transferred) ← transferAsset d prepared q.token q.recipient q.amount obs
  let w ← refundAsset transferred (w.core.rootAccountIdOf q.account) q.token q.amount debited
  return guardExit d { w with payouts := w.payouts ++ [⟨.approved, q.token, q.recipient,
    debited, none, some q⟩] }

/-- Deterministic measured credit selected only after observation checks succeed. -/
def receivedAmount (token : Key) (amount : Nat) (obs : TransferObservation) : Nat :=
  if token = 0 then amount else obs.afterBalance - obs.beforeBalance

/-- Deterministic measured debit; native callbacks may create surplus. -/
def debitedAmount (token : Key) (amount : Nat) (obs : TransferObservation) : Nat :=
  if token = 0 then amount else obs.beforeBalance - obs.afterBalance

inductive DepositTarget where
  | rootId (id : Nat)
  | owner (owner : Key)

/-- Shared checked allocation prefix of both deposit overloads. -/
def allocateDeposit (core : Core) : DepositTarget → Checked (Nat × Core)
  | .rootId id => do
    ensure (id < width 40) .config
    requireRoot core id
    pure (id, core)
  | .owner owner => ensureRoot core owner

/-- Both Core overloads converge on this source-ordered `_deposit` model. -/
def deposit (d : Deployment) (w : World) (_caller : Key) (target : DepositTarget)
    (token : Key) (amount msgValue : Nat) (obs : TransferObservation) : Checked World := do
  ensure (amount < width 256 ∧ msgValue < width 256) .config
  let w ← activeGuardEnter d w
  let (id, core) ← allocateDeposit w.core target
  let w := { w with core := core }
  ensure (amount > 0) .amount
  ensure ((w.core.tokens token).enabled = true) .token
  let w ← if token = 0 then do
    ensure (msgValue = amount) .transfer
    let custody ← checkedAdd 256 w.nativeCustody msgValue
    pure { w with nativeCustody := custody }
    else do
      ensure (msgValue = 0) .transfer
      ensure (obs.readsSucceed = true ∧ obs.beforeBalance < width 256) .transfer
      let w ← callbacks d obs.callbacks w
      ensure (obs.callSucceeds = true ∧ obs.afterBalance < width 256) .transfer
      ensure (obs.afterBalance > obs.beforeBalance ∧ obs.afterBalance - obs.beforeBalance ≤ amount) .transfer
      pure w
  let received := receivedAmount token amount obs
  requireLimiter w
  let (_, limiter) ← recordDeposit w.limiter w.now w.quotes d.coreAddress d.coreAddress
    token received (w.core.tokens token).decimals
  let balance ← checkedAdd 256 (w.core.balances id token) received
  return guardExit d { w with limiter := limiter, core := { w.core with
    balances := updateBalance w.core.balances id token balance } }

/-- Initialized proxy pair is then configured/bound through the real policy calls. -/
def freshBoundPair (d : Deployment) (now capacity rate : Nat)
    (owner feeCollector registry : Key) (roles : Key → Roles) : Checked World := do
  ensure (owner ≠ 0 ∧ feeCollector ≠ 0 ∧ d.coreAddress ≠ 0 ∧ d.codePresent d.coreAddress = true) .config
  let limiter ← initializeLimiter now capacity rate
  let (_, core) ← ensureRoot { owner := owner, feeCollector := feeCollector } feeCollector
  let w : World := { now := now, core := core, limiter := limiter, roles := roles }
  let w ← policyAction d w owner (.setRegistry registry)
  policyAction d w (roles registry).governance (.bindLimiter d.limiterAddress)

/-- Commits successful subcalls; catches restore ONLY the subcall's entry state. -/
def caughtCall (w : World) (action : World → Checked World) : World :=
  match action w with | .ok next => next | .error _ => w

inductive Entry where
  | ordinary (caller : Key) (args : OrdinaryArgs) (obs : TransferObservation)
  | approved (caller : Key) (args : ApprovedWithdrawal) (sig : SignatureAcceptance) (obs : TransferObservation)
  | funding (caller : Key) (target : DepositTarget) (token : Key) (amount msgValue : Nat) (obs : TransferObservation)
  | policy (caller : Key) (action : PolicyAction)
  | environment (action : EnvironmentAction)
  /-- External wrapper/router revert, not an AccountCore method. -/
  | abort (error : Error)

def invoke (d : Deployment) (w : World) : Entry → Checked World
  | .ordinary caller args obs => withdraw d w caller args obs
  | .approved caller args sig obs => fulfillApprovedWithdrawal d w caller args sig obs
  | .funding caller target token amount msgValue obs => deposit d w caller target token amount msgValue obs
  | .policy caller action => policyAction d w caller action
  | .environment action => .ok (environmentAction d w action)
  | .abort error => .error error

structure WithdrawalCall where
  caller : Key
  args : OrdinaryArgs
  observation : TransferObservation

def ordinaryBatch (d : Deployment) : List WithdrawalCall → World → Checked World
  | [], w => .ok w
  | c :: cs, w => do
    let next ← withdraw d w c.caller c.args c.observation
    ordinaryBatch d cs next

structure RouteCall where
  entry : Entry
  catchFailure : Bool

/-- An uncaught failure yields no partially committed state. -/
def route (d : Deployment) : List RouteCall → World → Checked World
  | [], w => .ok w
  | c :: cs, w =>
    match invoke d w c.entry with
    | .ok next => route d cs next
    | .error e => if c.catchFailure then route d cs w else .error e

/-- Reset is OUTER transaction-end only, never inside a custody function. -/
def endTransaction (w : World) : World :=
  { w with limiter := { w.limiter with transient := {} } }

def executeTransaction (d : Deployment) (w : World) (calls : List RouteCall) : World :=
  endTransaction (match route d calls w with | .ok next => next | .error _ => w)

/-- Environment lifecycle, not a nonexistent source payout guard. -/
def nextTransaction (w : World) (now : Nat) : Checked World := do
  ensure (w.now ≤ now) .history
  return { endTransaction w with now := now }

end Benchmark.Cases.Kuru.WithdrawalLimit
