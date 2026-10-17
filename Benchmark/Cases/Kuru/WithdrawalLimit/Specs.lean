/-
Private eight-group obligations for Kuru V2. These are SPECIFICATIONS, not proofs.
No axiom, assumed target invariant or ideal-expiry oracle is used by the model.
Reachability starts with fresh initialized/bound proxies and ghost EMPTY history.
The external frame/range boundary is named below; it does not assume limiter safety.
Theorem premises must be taken from the eventual proof statements, not advertised
as unconstrained solidity/bytecode safety. Every definition here is a Prop target.
-/
import Benchmark.Cases.Kuru.WithdrawalLimit.Contract

namespace Benchmark.Cases.Kuru.WithdrawalLimit

/-- Ghost full chronological history, not a lookup input or trusted E oracle. -/
def ghostWrite : List Checkpoint → Checkpoint → List Checkpoint
  | [], cp => [cp]
  | x :: [], cp => if x.timestamp = cp.timestamp then [cp] else [x, cp]
  | x :: y :: xs, cp => x :: ghostWrite (y :: xs) cp

/-- Exact cutoff second is INCLUDED. The logical sequence is retained in the result. -/
def expiredReference (xs : List Checkpoint) (now : Nat) : Nat × Nat :=
  if now < window then (0, 0) else
    (xs.foldl (fun (acc : (Nat × Nat) × Nat) cp =>
      ((if cp.timestamp ≤ now - window then (cp.cumulative, acc.2) else acc.1), acc.2 + 1))
      ((0, 0), 1)).1

def lastDeposit (xs : List Checkpoint) : Nat :=
  match xs.getLast? with | none => 0 | some cp => cp.cumulative

def lastTimestamp (xs : List Checkpoint) : Nat :=
  match xs.getLast? with | none => 0 | some cp => cp.timestamp

def chronological (xs : List Checkpoint) : Prop :=
  xs.Pairwise (fun a b => a.timestamp < b.timestamp ∧ a.cumulative ≤ b.cumulative)

def retainedOldest (latest : Nat) : Nat :=
  if latest > ringCapacity then latest - ringCapacity + 1 else 1

/-- Finite-array representation; does NOT contain the desired expiry equality. -/
def RingRepresentation (h : History) (xs : List Checkpoint) : Prop :=
  h.latestSequence = xs.length ∧ h.latestSequence < width 64 ∧
  h.referenceSequence ≤ h.latestSequence ∧ chronological xs ∧
  (∀ cp ∈ xs, cp.timestamp < width 64 ∧ cp.cumulative < width 192) ∧
  (∀ sequence, retainedOldest h.latestSequence ≤ sequence → sequence ≤ h.latestSequence →
    xs[sequence - 1]? = some (checkpointAt h sequence))

def FundingRepresentation (s : Persistent) (xs : List Checkpoint) (now : Nat) : Prop :=
  RingRepresentation s.history xs ∧
  current s.history = lastDeposit xs ∧
  s.cursor ≤ current s.history ∧ current s.history < width 192 ∧
  s.capacityUsd18 < width 128 ∧ s.rateUsd18 < width 128 ∧
  s.drip.available ≤ s.capacityUsd18 * usdScale ∧ s.drip.available < width 192 ∧
  s.drip.updatedAt < width 64 ∧ s.drip.updatedAt ≤ now ∧ lastTimestamp xs ≤ now

/-- Source-shaped account/balance manager boundary; no limiter invariant here. -/
def CoreRanges (c : Core) : Prop :=
  c.lastAccountId < width 40 ∧ c.epoch < width 64 ∧
  (∀ id, c.lastAccountId < id → (c.accounts id).rootId = 0) ∧
  (∀ k, c.approvedNonces k < width 256 ∧ (c.tokens k).decimals ≤ 77) ∧
  (∀ id k, c.balances id k < width 256 ∧ c.reserves id k < width 256) ∧
  (∀ id, (c.accounts id).rootId < width 40 ∧ (c.accounts id).subaccountSeq < width 16) ∧
  (∀ root, (c.subaccountsByRoot root).length < width 16 ∧
    ∀ position child, (c.subaccountsByRoot root)[position]? = some child →
      child ≤ c.lastAccountId ∧ (c.accounts child).rootId = root ∧
      (c.accounts child).owner = (c.accounts root).owner ∧
      (c.accounts child).subaccountSeq = position + 1) ∧
  (∀ id k, (c.grants id k).permissions < width 32 ∧ (c.grants id k).expiry < width 64) ∧
  (∀ owner, let id := c.rootAccountIdOf owner
    id < width 40 ∧ (id ≠ 0 → (c.accounts id).rootId = id ∧ (c.accounts id).owner = owner))

def FrameAdmissible (f : InternalFrame) : Prop :=
  (∀ id k, f.balances id k < width 256 ∧ f.reserves id k < width 256) ∧
  (∀ id k, (f.grants id k).permissions < width 32 ∧ (f.grants id k).expiry < width 64)

def EnvironmentAdmissible : EnvironmentAction → Prop
  | .internalFrame f => FrameAdmissible f
  | _ => True

def CallbacksAdmissible (obs : TransferObservation) : Prop :=
  ∀ cb ∈ obs.callbacks, ∀ a ∈ cb.environmentBefore, EnvironmentAdmissible a

def EntryAdmissible : Entry → Prop
  | .ordinary _ _ obs => CallbacksAdmissible obs
  | .approved _ _ _ obs => CallbacksAdmissible obs
  | .funding _ _ _ _ _ obs => CallbacksAdmissible obs
  | .environment a => EnvironmentAdmissible a
  | .policy _ _ => True
  | .abort _ => True

/-- Ghost changes only when an actual committed custody deposit grows D. -/
def nextGhost (xs : List Checkpoint) (before after : World) : List Checkpoint :=
  if current after.limiter.persistent.history > current before.limiter.persistent.history then
    ghostWrite xs ⟨after.now, current after.limiter.persistent.history⟩
  else xs

/-- No initial RingRepresentation/FundingRepresentation/withdrawal result premise. -/
inductive Reachable (d : Deployment) : World → List Checkpoint → Prop where
  | initialized (now capacity rate : Nat) (owner feeCollector registry : Key)
      (roles : Key → Roles) (w : World)
      (h : freshBoundPair d now capacity rate owner feeCollector registry roles = .ok w) :
      Reachable d w []
  | success (w next : World) (xs : List Checkpoint) (entry : Entry)
      (hr : Reachable d w xs) (ha : EntryAdmissible entry)
      (h : invoke d w entry = .ok next) : Reachable d next (nextGhost xs w next)
  | caughtFailure (w : World) (xs : List Checkpoint) (entry : Entry) (err : Error)
      (hr : Reachable d w xs) (h : invoke d w entry = .error err) : Reachable d w xs
  | endTx (w : World) (xs : List Checkpoint) (hr : Reachable d w xs) :
      Reachable d (endTransaction w) xs
  | newTx (w next : World) (xs : List Checkpoint) (now : Nat)
      (hr : Reachable d w xs) (h : nextTransaction w now = .ok next) : Reachable d next xs

/-- Group 1: initialization AND derived representation after every relevant writer. -/
def InitializationAndWriterClosure : Prop :=
  (∀ d now capacity rate owner fee registry roles w,
    freshBoundPair d now capacity rate owner fee registry roles = .ok w →
    current w.limiter.persistent.history = 0 ∧ w.limiter.persistent.cursor = 0 ∧
    w.limiter.persistent.history.latestSequence = 0 ∧
    w.limiter.persistent.drip.available = capacity * usdScale ∧
    w.limiter.transient.flowStarted = false ∧ w.core.limiterBound = true) ∧
  (∀ d w xs, Reachable d w xs → FundingRepresentation w.limiter.persistent xs w.now) ∧
  (∀ d w xs, Reachable d w xs → CoreRanges w.core) ∧
  (∀ d w xs, Reachable d w xs →
    w.limiter.transient.flowStarted = true →
    w.limiter.transient.expired = (expiredReference xs w.now).1)

/-- All ring branches, widths, same-second update, wrap and sequence overflow. -/
def ExactHistoryCorrespondence : Prop :=
  (∀ h xs now, RingRepresentation h xs → lastTimestamp xs ≤ now →
    now < width 64 → referenceAt h now = .ok (expiredReference xs now)) ∧
  (∀ h xs now v next, RingRepresentation h xs → lastTimestamp xs ≤ now →
    v ≥ current h → write h v now = .ok next →
    RingRepresentation next (ghostWrite xs ⟨now, v⟩) ∧ current next = v) ∧
  (∀ sequence other latest, retainedOldest latest ≤ sequence → sequence ≤ latest →
    retainedOldest latest ≤ other → other ≤ latest →
    (sequence - 1) % ringCapacity = (other - 1) % ringCapacity → sequence = other) ∧
  (∀ h v now, h.latestSequence = maxWord 64 →
    now > (checkpointAt h h.latestSequence).timestamp →
    v ≤ maxWord 192 → now ≤ maxWord 64 →
    v ≥ current h → write h v now = .error .arithmetic) ∧
  (∀ cp, cp.timestamp < width 64 → cp.cumulative < width 192 →
    unpackCheckpoint (packCheckpoint cp) = cp)

/-- Group 3: exact full-product valuation and conservative integer rounding. -/
def ValuationAndWidths : Prop :=
  (∀ amount quote decimals up v, value amount quote decimals up = .ok v →
    v ≤ maxWord 192 ∧
    (decimals ≤ 18 → v = amount * quote * 10 ^ (18 - decimals)) ∧
    (decimals > 18 →
      let divisor := 10 ^ (decimals - 18)
      if up then amount * quote ≤ v * divisor ∧ v * divisor < amount * quote + divisor
      else v * divisor ≤ amount * quote ∧ amount * quote < (v + 1) * divisor)) ∧
  (∀ amount quote decimals, decimals > 18 → decimals ≤ 77 →
    quote > 0 → quote < width 128 → amount < width 256 →
    amount * quote < 10 ^ (decimals - 18) → value amount quote decimals false = .ok 0) ∧
  (maxWord 128 * usdScale < width 192) ∧
  (maxWord 192 + maxWord 64 * maxWord 128 * usdScale < width 256) ∧
  (∀ drip, drip.available < width 192 → drip.updatedAt < width 64 →
    unpackDrip (packDrip drip) = drip) ∧
  (∀ D cursor used, D < width 192 → cursor ≤ D → used ≤ D - cursor →
    castWord 192 (cursor + used) = cursor + used)

/-- Stable fields for pool preservation; caches are intentionally excluded. -/
def SameFundingPools (before after : Limiter) : Prop :=
  current after.persistent.history = current before.persistent.history ∧
  after.persistent.cursor = before.persistent.cursor ∧
  after.persistent.drip = before.persistent.drip

def SamePersistent (before after : Limiter) : Prop := after.persistent = before.persistent

/-- Group 4: actual snapshots, no per-call transient reset, atomicity and fixed time. -/
def TransactionAndSnapshots : Prop :=
  (∀ d w entry next, invoke d w entry = .ok next → next.now = w.now) ∧
  (∀ s now next, s.transient.flowStarted = true → beginFlow s now = .ok next → next = s) ∧
  (∀ h xs now s next, RingRepresentation h xs → lastTimestamp xs ≤ now → now < width 64 →
    s.persistent.history = h → s.transient.flowStarted = false → beginFlow s now = .ok next →
    next.transient.expired = (expiredReference xs now).1 ∧ next.transient.flowStarted = true ∧
    next.persistent.history.referenceSequence = (expiredReference xs now).2) ∧
  (∀ s fetch token quote next, snapshotPrice s fetch token = .ok (quote, next) →
    next.transient.prices token = quote ∧ SamePersistent s next) ∧
  (∀ s token cached fetch, s.transient.prices token = cached → cached ≠ 0 →
    price s fetch token = .ok (castWord 128 cached)) ∧
  (∀ w, SamePersistent w.limiter (endTransaction w).limiter ∧
    (endTransaction w).limiter.transient.flowStarted = false ∧
    (∀ k, (endTransaction w).limiter.transient.prices k = 0)) ∧
  (∀ w action err, action w = .error err → caughtCall w action = w) ∧
  (∀ d w calls err, route d calls w = .error err →
    executeTransaction d w calls = endTransaction w) ∧
  (∀ d w precedingCalls subroute previous err, route d precedingCalls w = .ok previous →
    route d subroute previous = .error err →
    caughtCall previous (fun s => route d subroute s) = previous)

/-- Valued gross ordinary payouts, not custody net-delta or recipient proceeds. -/
def ordinaryGrossValues (ps : List Payout) : Nat :=
  ps.foldl (fun total p => total + match p.funding with | some f => f.value | none => 0) 0

/-- Central business rule AND exact source-conditional post-state equations. -/
def OrdinaryConsumption (before after : Limiter) (now expired : Nat) (f : Funding) : Prop :=
  let D := current before.persistent.history
  let cursor := max expired before.persistent.cursor
  let C := D - cursor
  ∃ A, availableDrip before.persistent now = .ok A ∧
    f.cursor = cursor ∧ f.credit = C ∧ f.depositUsed = min f.value C ∧
    f.dripUsed = f.value - f.depositUsed ∧ f.value ≤ C + A ∧
    current after.persistent.history = D ∧
    after.persistent.cursor = (if f.depositUsed ≠ 0 then cursor + f.depositUsed else before.persistent.cursor) ∧
    after.persistent.drip = (if f.dripUsed ≠ 0 then ⟨A - f.dripUsed, now⟩ else before.persistent.drip) ∧
    D - max expired after.persistent.cursor = C - f.depositUsed ∧
    availableDrip after.persistent now = .ok (A - f.dripUsed)

/-- Runtime checkpoints in Core.withdraw, not trust in users/token recipients. -/
def OrdinaryCheckpoints (d : Deployment) (w : World) (caller : Key) (a : OrdinaryArgs) : Prop :=
  w.core.paused = false ∧ w.core.guardWord ≠ d.coreAddress.toNat ∧
  (w.core.accounts a.rootId).rootId ≠ 0 ∧ (w.core.accounts a.rootId).rootId = a.rootId ∧
  withdrawAuthorized w.core w.now a.rootId caller = true ∧ a.amount > 0 ∧
  a.recipient ≠ 0 ∧ a.recipient ≠ d.coreAddress ∧ w.core.balances a.rootId a.token ≥ a.amount ∧
  w.core.frozen = false ∧ w.core.tokenFrozen a.token = false ∧ w.core.limiterBound = true

/-- No token/root budget argument exists: all calls debit the SAME persistent state.
    Batch capacity equations require a successful initial capacity observation.
    An empty batch can succeed when the separate timestamp-checked view fails. -/
def OrdinaryAndGlobalNoReuse : Prop :=
  (∀ d w xs token amount decimals f next, Reachable d w xs →
    recordWithdrawal w.limiter w.now w.quotes d.coreAddress d.coreAddress token amount decimals = .ok (f, next) →
    OrdinaryConsumption w.limiter next w.now (expiredReference xs w.now).1 f) ∧
  (∀ d w xs caller args obs next, Reachable d w xs → CallbacksAdmissible obs →
    withdraw d w caller args obs = .ok next →
    OrdinaryCheckpoints d w caller args ∧
    ∃ f, next.payouts = w.payouts ++ [⟨.ordinary, args.token, args.recipient, debitedAmount args.token args.amount obs, some f, none⟩] ∧
    OrdinaryConsumption w.limiter next.limiter w.now (expiredReference xs w.now).1 f) ∧
  (∀ d w xs calls next C A, Reachable d w xs →
    capacityState w.limiter w.now = .ok (C, A) →
    (∀ c ∈ calls, CallbacksAdmissible c.observation) → ordinaryBatch d calls w = .ok next →
    ∃ Cnew Anew, capacityState next.limiter next.now = .ok (Cnew, Anew) ∧
      Cnew + Anew + (ordinaryGrossValues next.payouts - ordinaryGrossValues w.payouts) = C + A) ∧
  (∀ (D E S Enew Snew : Nat), S ≤ D → E ≤ D → Enew ≤ D → Snew ≤ D →
    E ≤ Enew → S ≤ Snew → D - max Enew Snew ≤ D - max E S) ∧
  (∀ w, (endTransaction w).limiter.persistent.cursor = w.limiter.persistent.cursor ∧
    (endTransaction w).limiter.persistent.drip = w.limiter.persistent.drip) ∧
  (∀ d w xs token amount decimals v next, Reachable d w xs →
    recordDeposit w.limiter w.now w.quotes d.coreAddress d.coreAddress token amount decimals = .ok (v, next) →
    current next.persistent.history = current w.limiter.persistent.history + v ∧
    next.persistent.cursor = w.limiter.persistent.cursor ∧ next.persistent.drip = w.limiter.persistent.drip)

/-- Group 6: settlement uses OLD configuration, no instant capacity grant. -/
def DripAndConfiguration : Prop :=
  (∀ s now A, availableDrip s now = .ok A →
    A = min (s.drip.available + (now - s.drip.updatedAt) * s.rateUsd18 * usdScale)
      (s.capacityUsd18 * usdScale)) ∧
  (∀ s now caller governance capacity rate next A,
    availableDrip s.persistent now = .ok A →
    setDripConfig s now caller governance capacity rate = .ok next →
    next.persistent.drip.available = min A (capacity * usdScale) ∧
    next.persistent.drip.updatedAt = now ∧ next.persistent.capacityUsd18 = capacity ∧
    next.persistent.rateUsd18 = rate ∧ next.persistent.history = s.persistent.history ∧
    next.persistent.cursor = s.persistent.cursor ∧ next.persistent.drip.available ≤ A) ∧
  (∀ s now caller governance capacity rate, s.transient.flowStarted = true →
    caller = governance → setDripConfig s now caller governance capacity rate = .error .config) ∧
  (∀ s caller governance token source code, s.transient.flowStarted = true →
    caller = governance → setPriceSource s caller governance token source code = .error .config)

/-- All fields are checkpoint facts, NOT equalities to callback-modified final state. -/
def ApprovedCheckpoints (d : Deployment) (w : World) (caller : Key)
    (q : ApprovedWithdrawal) (sig : SignatureAcceptance) : Prop :=
  w.core.paused = false ∧ w.core.guardWord ≠ d.coreAddress.toNat ∧
  (w.core.accounts (w.core.rootAccountIdOf q.account)).rootId ≠ 0 ∧
  (w.core.accounts (w.core.rootAccountIdOf q.account)).rootId = w.core.rootAccountIdOf q.account ∧
  q.amount ≠ 0 ∧ q.recipient ≠ 0 ∧ q.recipient ≠ d.coreAddress ∧
  w.core.balances (w.core.rootAccountIdOf q.account) q.token ≥ q.amount ∧ w.core.limiterBound = true ∧
  caller = w.core.authority ∧ caller ≠ 0 ∧ q.authorityEpoch = w.core.epoch ∧
  q.nonce = w.core.approvedNonces q.account ∧ w.now ≤ q.deadline ∧
  signatureValid d (w.core.accounts (w.core.rootAccountIdOf q.account)).owner q sig = true ∧
  w.core.frozen = false ∧ w.core.tokenFrozen q.token = false

/-- Approved payout amount is not valued. Nonce after callback may be GREATER. -/
def ApprovedAuthorityAndReplay : Prop :=
  (∀ d w caller q sig checkpoint, approvedBeforeTransfer d w caller q sig = .ok checkpoint →
    ApprovedCheckpoints d w caller q sig ∧
    checkpoint.core.approvedNonces q.account = q.nonce + 1 ∧
    checkpoint.core.balances (w.core.rootAccountIdOf q.account) q.token =
      w.core.balances (w.core.rootAccountIdOf q.account) q.token - q.amount ∧
    checkpoint.core.guardWord = d.coreAddress.toNat ∧ SameFundingPools w.limiter checkpoint.limiter) ∧
  (∀ d w xs caller q sig obs next, Reachable d w xs → CallbacksAdmissible obs →
    fulfillApprovedWithdrawal d w caller q sig obs = .ok next →
    ApprovedCheckpoints d w caller q sig ∧
    q.nonce + 1 ≤ next.core.approvedNonces q.account ∧
    SameFundingPools w.limiter next.limiter ∧
    next.payouts = w.payouts ++ [⟨.approved, q.token, q.recipient, debitedAmount q.token q.amount obs, none, some q⟩]) ∧
  (∀ d w caller account n next, policyAction d w caller (.invalidateNonce account n) = .ok next →
    next.core.approvedNonces account = n ∧ w.core.approvedNonces account < n) ∧
  (∀ d w caller authority next, policyAction d w caller (.rotateAuthority authority) = .ok next →
    next.core.epoch = w.core.epoch + 1) ∧
  (∀ d w caller q sig obs first second,
    fulfillApprovedWithdrawal d w caller q sig obs = .ok first →
    fulfillApprovedWithdrawal d first caller q sig obs ≠ .ok second)

/-- General successful deposit: credit and limiter input are the SAME positive
    measured receipt, added to the post-callback ledger (not the entry ledger). -/
def MeasuredDepositCredit : Prop :=
  ∀ d w caller target token amount msgValue obs next,
    deposit d w caller target token amount msgValue obs = .ok next →
    let received := receivedAmount token amount obs
    0 < received ∧ received ≤ amount ∧
    ∃ entered id core funded v limiter,
      activeGuardEnter d w = .ok entered ∧
      allocateDeposit entered.core target = .ok (id, core) ∧
      (if token = 0 then ∃ custody,
        checkedAdd 256 entered.nativeCustody msgValue = .ok custody ∧
        funded = { entered with core := core, nativeCustody := custody }
       else callbacks d obs.callbacks { entered with core := core } = .ok funded) ∧
      recordDeposit funded.limiter funded.now funded.quotes d.coreAddress d.coreAddress
        token received (funded.core.tokens token).decimals = .ok (v, limiter) ∧
      next = guardExit d { funded with limiter := limiter, core := { funded.core with
        balances := updateBalance funded.core.balances id token (funded.core.balances id token + received) } }

/-- Exact ordinary settlement witnesses are source checkpoints, not arbitrary
    balances. In particular the refund uses transferred.core, and capacity is
    recorded only AFTER it, with post-callback decimals and the actual debit. -/
def MeasuredOrdinarySettlement : Prop :=
  ∀ d w caller a obs next, withdraw d w caller a obs = .ok next →
    let debit := debitedAmount a.token a.amount obs
    0 < debit ∧ debit ≤ a.amount ∧
    ∃ entered prepared transferred refunded funding limiter,
      activeGuardEnter d w = .ok entered ∧
      withdrawBeforeTransfer d entered a.rootId a.token a.amount = .ok prepared ∧
      prepared.limiter.transient.flowStarted = true ∧
      transferAsset d prepared a.token a.recipient a.amount obs = .ok (debit, transferred) ∧
      transferred.limiter = prepared.limiter ∧
      refundAsset transferred a.rootId a.token a.amount debit = .ok refunded ∧
      refunded.core.balances a.rootId a.token =
        transferred.core.balances a.rootId a.token + (a.amount - debit) ∧
      recordWithdrawal refunded.limiter refunded.now refunded.quotes d.coreAddress d.coreAddress
        a.token debit (refunded.core.tokens a.token).decimals = .ok (funding, limiter) ∧
      next = guardExit d { refunded with limiter := limiter, payouts := refunded.payouts ++
        [⟨.ordinary, a.token, a.recipient, debit, some funding, none⟩] }

/-- Approved debit is bounded by the signed maximum; the complete signed request
    survives in the instruction receipt, while the Withdrawal receipt is actual. -/
def MeasuredApprovedSettlement : Prop :=
  ∀ d w caller q sig obs next, fulfillApprovedWithdrawal d w caller q sig obs = .ok next →
    let debit := debitedAmount q.token q.amount obs
    0 < debit ∧ debit ≤ q.amount ∧
    ∃ prepared transferred refunded,
      approvedBeforeTransfer d w caller q sig = .ok prepared ∧
      prepared.limiter.transient.flowStarted = true ∧
      transferAsset d prepared q.token q.recipient q.amount obs = .ok (debit, transferred) ∧
      transferred.limiter = prepared.limiter ∧
      refundAsset transferred (w.core.rootAccountIdOf q.account) q.token q.amount debit = .ok refunded ∧
      refunded.core.balances (w.core.rootAccountIdOf q.account) q.token =
        transferred.core.balances (w.core.rootAccountIdOf q.account) q.token + (q.amount - debit) ∧
      next = guardExit d { refunded with payouts := refunded.payouts ++
        [⟨.approved, q.token, q.recipient, debit, none, some q⟩] }

/-- Group 8: physical path inventory, rollback, actual guard, and surplus framing. -/
def PayoutCoverageAndAtomicity : Prop :=
  (∀ d w xs entry next, Reachable d w xs → EntryAdmissible entry → invoke d w entry = .ok next →
    (next.payouts = w.payouts ∨
      ∃ p, next.payouts = w.payouts ++ [p] ∧
        ((p.kind = .ordinary ∧ p.funding.isSome = true) ∨
         (p.kind = .approved ∧ p.approvedInstruction.isSome = true)))) ∧
  (∀ d w caller, w.core.guardWord = d.coreAddress.toNat →
    w.core.paused = false → policyAction d w caller .nestedGuarded = .error .reentrant) ∧
  (∀ d w caller amount next, policyAction d w caller (.receiveNative amount) = .ok next →
    next.limiter = w.limiter ∧ next.payouts = w.payouts ∧
    next.nativeCustody = w.nativeCustody + amount) ∧
  (∀ w f, (applyInternalFrame w f).limiter = w.limiter ∧
    (applyInternalFrame w f).payouts = w.payouts ∧
    (applyInternalFrame w f).nativeCustody = w.nativeCustody) ∧
  (∀ d w entry err, invoke d w entry = .error err → caughtCall w (fun s => invoke d s entry) = w) ∧
  (∀ d w calls err, route d calls w = .error err →
    (executeTransaction d w calls).core = w.core ∧
    (executeTransaction d w calls).limiter.persistent = w.limiter.persistent ∧
    (executeTransaction d w calls).nativeCustody = w.nativeCustody ∧
    (executeTransaction d w calls).payouts = w.payouts) ∧
  MeasuredDepositCredit ∧ MeasuredOrdinarySettlement ∧ MeasuredApprovedSettlement

/-- Full target; passing only one conjunct is NOT the client's completed result. -/
def PolicyBundle : Prop :=
  InitializationAndWriterClosure ∧ ExactHistoryCorrespondence ∧ ValuationAndWidths ∧
  TransactionAndSnapshots ∧ OrdinaryAndGlobalNoReuse ∧ DripAndConfiguration ∧
  ApprovedAuthorityAndReplay ∧ PayoutCoverageAndAtomicity

end Benchmark.Cases.Kuru.WithdrawalLimit
