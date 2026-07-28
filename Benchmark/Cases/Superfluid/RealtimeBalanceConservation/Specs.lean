import Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Contract

namespace Benchmark.Cases.Superfluid.RealtimeBalanceConservation

open Verity
open Verity.EVM.Uint256

/-- The CFA linear accounting projection at a timestamp.
This is not the native multi-agreement `realtimeBalanceOf` available balance. -/
def cfaProjectionAt (s : ContractState) (account : Address) (timestamp : Uint256) : Uint256 :=
  add (s.storageMap 0 account)
    (mul (sub timestamp (s.storageMap 2 account)) (s.storageMap 1 account))

/-- Combined CFA projection of one flow's two endpoints. -/
def pairCfaProjectionAt
    (s : ContractState) (sender receiver : Address) (timestamp : Uint256) : Uint256 :=
  add (cfaProjectionAt s sender timestamp) (cfaProjectionAt s receiver timestamp)

/-- Combined signed-word net flow rate of one flow's two endpoints. -/
def pairNetFlowRate (s : ContractState) (sender receiver : Address) : Uint256 :=
  add (s.storageMap 1 sender) (s.storageMap 1 receiver)

/-- Fixed finite-universe CFA-only projection sum. Every addition and the dynamic
`sub`/`mul` inside `cfaProjectionAt` is `Uint256` arithmetic modulo `2^256`.
This is not an unbounded-`Int` sum, native multi-agreement realtime balance,
SuperToken total supply, or a full-protocol conservation quantity. -/
def modularCfaGlobalProjectionSumAt
    (s : ContractState) (accounts : List Address) (timestamp : Uint256) : Uint256 :=
  (accounts.map (fun account => cfaProjectionAt s account timestamp)).sum

/-- A duplicate-free fixed universe that counts two distinct touched endpoints once. -/
def CfaPairCoveredBy
    (accounts : List Address) (sender receiver : Address) : Prop :=
  accounts.Nodup ∧ sender ≠ receiver ∧ sender ∈ accounts ∧ receiver ∈ accounts

/-- Reusable local-to-global statement: endpoint cancellation plus framing every
other member of a duplicate-free universe implies preservation of its modular sum. -/
def pairAndFrameImplyModularCfaGlobalProjection
    (pre post : ContractState) (accounts : List Address)
    (sender receiver : Address) (timestamp : Uint256) : Prop :=
  CfaPairCoveredBy accounts sender receiver →
  pairCfaProjectionAt post sender receiver timestamp =
    pairCfaProjectionAt pre sender receiver timestamp →
  (∀ account, account ∈ accounts → account ≠ sender → account ≠ receiver →
    cfaProjectionAt post account timestamp = cfaProjectionAt pre account timestamp) →
  modularCfaGlobalProjectionSumAt post accounts timestamp =
    modularCfaGlobalProjectionSumAt pre accounts timestamp

/-- Stored decoded pair flow rate. -/
def storedFlowRate (s : ContractState) (sender receiver : Address) : Uint256 :=
  s.storageMap2 6 sender receiver

/-- Pinned source storage/context values related to the decoded Verity state. -/
structure PinnedSourceState where
  sharedSettled : Address → Uint256
  accountFlowWord : Address → Uint256
  pairFlowWord : Address → Address → Uint256
  flowKeyMatches : Address → Address → Uint256
  cfaOnlyActiveAgreement : Uint256
  governanceLiquidationPeriod : Uint256
  governanceMinimumDeposit : Uint256
  hostIsApp : Address → Uint256
  hostIsJailed : Address → Uint256
  hostBeforeCreatedNoop : Address → Uint256
  hostAfterCreatedEnabled : Address → Uint256
  hostCallbackCreditUsed : Address → Uint256
  hostCallbackLevel : Address → Uint256
  hostCallbackActor : Address → Uint256
  hostCallbackAppAddress : Address → Uint256
  hostIsAppCallbackContext : Address → Uint256
  hostContextualDeleteEnabled : Address → Uint256
  hostNestedCallbackSuppressed : Address → Uint256
  hostAppCreditTokenMatches : Address → Uint256
  hostAppCreditGranted : Address → Uint256
  hostAdditionalAppCredit : Address → Uint256
  hostIsSelfDeletingFlowApp : Address → Uint256
  hostOuterIsDirectCallContext : Uint256
  hostOuterAppCreditToken : Uint256
  hostOuterActor : Uint256

/-- Exact `_encodeFlowData` arithmetic over decoded fields. -/
def packFlowData
    (timestamp flowRate deposit owedDeposit : Uint256) : Uint256 :=
  add (mul timestamp
      26959946667150639794667015087019630673637144422540572481103610249216)
    (add (mul (mod flowRate 79228162514264337593543950336)
        340282366920938463463374607431768211456)
      (add (mul (div deposit 4294967296) 18446744073709551616)
        (div owedDeposit 4294967296)))

/-- Packed Solidity source state, SuperToken storage, CFA key/existence, Host context,
and governance values all refine the decoded Verity state for the touched pair. -/
def sourceModelRelation
    (source : PinnedSourceState) (s : ContractState)
    (sender receiver : Address) : Prop :=
  source.sharedSettled sender = s.storageMap 0 sender ∧
  source.sharedSettled receiver = s.storageMap 0 receiver ∧
  source.accountFlowWord sender = packFlowData
    (s.storageMap 2 sender) (s.storageMap 1 sender)
    (s.storageMap 3 sender) (s.storageMap 4 sender) ∧
  source.accountFlowWord receiver = packFlowData
    (s.storageMap 2 receiver) (s.storageMap 1 receiver)
    (s.storageMap 3 receiver) (s.storageMap 4 receiver) ∧
  source.pairFlowWord sender receiver = packFlowData
    (s.storageMap2 5 sender receiver) (s.storageMap2 6 sender receiver)
    (s.storageMap2 7 sender receiver) (s.storageMap2 8 sender receiver) ∧
  (source.pairFlowWord sender receiver > 0 ↔ s.storageMap2 9 sender receiver = 1) ∧
  source.flowKeyMatches sender receiver = s.storageMap2 27 sender receiver ∧
  source.cfaOnlyActiveAgreement = s.storage 26 ∧
  source.cfaOnlyActiveAgreement = 1 ∧
  source.governanceLiquidationPeriod = s.storage 24 ∧
  source.governanceMinimumDeposit = s.storage 25 ∧
  source.hostIsApp sender = s.storageMap 10 sender ∧
  source.hostIsApp receiver = s.storageMap 10 receiver ∧
  source.hostIsJailed receiver = s.storageMap 11 receiver ∧
  source.hostBeforeCreatedNoop receiver = s.storageMap 12 receiver ∧
  source.hostAfterCreatedEnabled receiver = s.storageMap 13 receiver ∧
  source.hostCallbackCreditUsed receiver = s.storageMap 14 receiver ∧
  source.hostCallbackLevel receiver = s.storageMap 15 receiver ∧
  source.hostCallbackActor receiver = s.storageMap 16 receiver ∧
  source.hostCallbackAppAddress receiver = s.storageMap 17 receiver ∧
  source.hostIsAppCallbackContext receiver = s.storageMap 18 receiver ∧
  source.hostContextualDeleteEnabled receiver = s.storageMap 19 receiver ∧
  source.hostNestedCallbackSuppressed receiver = s.storageMap 20 receiver ∧
  source.hostAppCreditTokenMatches receiver = s.storageMap 21 receiver ∧
  source.hostAppCreditGranted receiver = s.storageMap 22 receiver ∧
  source.hostAdditionalAppCredit receiver = s.storageMap 23 receiver ∧
  source.hostIsSelfDeletingFlowApp receiver = s.storageMap 28 receiver ∧
  source.hostOuterIsDirectCallContext = s.storage 29 ∧
  source.hostOuterAppCreditToken = s.storage 30 ∧
  source.hostOuterActor = s.storage 31

/-- Source post-state transformer for the selected transition: update only the source
fields written by CFA/SuperToken accounting and retain keying, governance, and Host
environment facts from the actual source pre-state. -/
def repackSourcePost
    (source : PinnedSourceState) (post : ContractState)
    (sender receiver : Address) : PinnedSourceState :=
  { source with
    sharedSettled := fun account =>
      if account == sender then post.storageMap 0 sender
      else if account == receiver then post.storageMap 0 receiver
      else source.sharedSettled account
    accountFlowWord := fun account =>
      if account == sender then packFlowData
        (post.storageMap 2 sender) (post.storageMap 1 sender)
        (post.storageMap 3 sender) (post.storageMap 4 sender)
      else if account == receiver then packFlowData
        (post.storageMap 2 receiver) (post.storageMap 1 receiver)
        (post.storageMap 3 receiver) (post.storageMap 4 receiver)
      else source.accountFlowWord account
    pairFlowWord := fun left right =>
      if left == sender && right == receiver then packFlowData
        (post.storageMap2 5 sender receiver) (post.storageMap2 6 sender receiver)
        (post.storageMap2 7 sender receiver) (post.storageMap2 8 sender receiver)
      else source.pairFlowWord left right }

/-- Apply the selected source accounting transformer to the actual pinned pre-state and
require its packed post-state to refine the decoded model post-state. -/
def sourcePostRelation
    (source : PinnedSourceState) (post : ContractState)
    (sender receiver : Address) : Prop :=
  sourceModelRelation (repackSourcePost source post sender receiver)
    post sender receiver

/-- The source-level account representation and checked-arithmetic relation used by public claims.
Executable contract guards enforce packing, timestamps, and int96 rate bounds. These
additional propositions retain the two checked signed operations that the EVM-word
model intentionally proves over a larger modular domain. -/
def sourceAccountRelationAt
    (s : ContractState) (account : Address) (timestamp : Uint256) : Prop :=
  s.storageMap 2 account ≤ 4294967295 ∧
  isCanonicalInt96Word (s.storageMap 1 account) = true ∧
  isPackedDepositWord (s.storageMap 3 account) = true ∧
  s.storageMap 4 account = 0 ∧
  s.storageMap 2 account ≤ timestamp ∧
  let dynamicWord := mul (sub timestamp (s.storageMap 2 account)) (s.storageMap 1 account)
  signedAddNoOverflow (s.storageMap 0 account) dynamicWord = true ∧
  signedSubNoOverflow (add (s.storageMap 0 account) dynamicWord)
    (s.storageMap 3 account) = true

/-- Source relation for both endpoints of the represented CFA-only slice. -/
def sourceEndpointRelationAt
    (s : ContractState) (sender receiver : Address) (timestamp : Uint256) : Prop :=
  sourceAccountRelationAt s sender timestamp ∧
  sourceAccountRelationAt s receiver timestamp

/-- Complete pre-state refinement and checked-arithmetic relation for a touched pair. -/
def pinnedSourcePathRelation
    (source : PinnedSourceState) (s : ContractState)
    (sender receiver : Address) (timestamp : Uint256) : Prop :=
  sourceModelRelation source s sender receiver ∧
  sourceEndpointRelationAt s sender receiver timestamp ∧
  source.hostIsJailed receiver = 0

/-- The decoded Verity execution completed without reverting. Source-path claims
also require `pinnedSourcePathRelation`; this predicate alone is only model success. -/
def modelSucceeded {α : Type} (result : ContractResult α) : Prop :=
  result.isSuccess = true

/-- Explicit source/Host bindings retained by the concrete SelfDeleting callback.
The `hostNestedCallbackSuppressed` field records the selected CFA same-flow receiver
delete's `appToCallback = 0` branch; generic level-2 rejection is a separate behavior.
Token identity is represented by the decoded outer-zero-token and same-credit-token
facts because this protocol slice does not carry a standalone token address parameter. -/
def ConcreteSelfDeletingCallbackGuards
    (source : PinnedSourceState) (sender receiver : Address)
    (flowRate liquidationPeriod minimumDeposit : Uint256) : Prop :=
  source.hostIsApp receiver = 1 ∧
  source.hostIsApp sender = 0 ∧
  source.hostIsJailed receiver = 0 ∧
  source.hostBeforeCreatedNoop receiver = 1 ∧
  source.hostAfterCreatedEnabled receiver = 1 ∧
  source.hostCallbackCreditUsed receiver = 0 ∧
  source.hostCallbackLevel receiver = 1 ∧
  source.hostCallbackActor receiver = receiver ∧
  source.hostCallbackAppAddress receiver = receiver ∧
  source.hostIsAppCallbackContext receiver = 1 ∧
  source.hostContextualDeleteEnabled receiver = 1 ∧
  source.hostNestedCallbackSuppressed receiver = 1 ∧
  source.hostAppCreditTokenMatches receiver = 1 ∧
  source.hostIsSelfDeletingFlowApp receiver = 1 ∧
  source.hostOuterIsDirectCallContext = 1 ∧
  source.hostOuterAppCreditToken = 0 ∧
  source.hostOuterActor = sender ∧
  let appCreditBase := clipDepositRoundingUp (mul flowRate liquidationPeriod)
  if appCreditBase = 0 then
    source.hostAdditionalAppCredit receiver = 0 ∧
    source.hostAppCreditGranted receiver = 0
  else
    source.hostAdditionalAppCredit receiver ≥ 4294967296 ∧
    source.hostAdditionalAppCredit receiver ≥ minimumDeposit ∧
    (source.hostAdditionalAppCredit receiver = 4294967296 ∨
      source.hostAdditionalAppCredit receiver = minimumDeposit) ∧
    source.hostAppCreditGranted receiver =
      add appCreditBase (source.hostAdditionalAppCredit receiver)

/-- A component preserves the fixed-universe modular CFA projection on every
successful execution. Reverting executions are not reclassified as successes. -/
def PreservesModularCfaGlobalProjection {α : Type}
    (accounts : List Address) (timestamp : Uint256) (op : Contract α) : Prop :=
  ∀ pre value post,
    op.run pre = ContractResult.success value post →
    modularCfaGlobalProjectionSumAt post accounts timestamp =
      modularCfaGlobalProjectionSumAt pre accounts timestamp

/-- Successful prefix, nested, and resume components compose through the executable
level-1 hook. Component obligations range over their actual typed intermediate values. -/
def successfulOneLevelComponentsCompose {α β γ : Type}
    (outerPrefix : Contract α) (nested : α → Contract β)
    (outerResume : α → β → Contract γ)
    (accounts : List Address) (timestamp : Uint256) : Prop :=
  PreservesModularCfaGlobalProjection accounts timestamp outerPrefix →
  (∀ prefixValue,
    PreservesModularCfaGlobalProjection accounts timestamp (nested prefixValue)) →
  (∀ prefixValue nestedValue,
    PreservesModularCfaGlobalProjection accounts timestamp
      (outerResume prefixValue nestedValue)) →
  PreservesModularCfaGlobalProjection accounts timestamp
    (runOneLevelOuterNested outerPrefix nested outerResume)

/-- The behavioral hook rejects callback level 2 before the supplied nested program.
This models the pinned Host maximum-level discipline, not full Host ABI/context checks. -/
def callbackLevelTwoRejected : Prop :=
  ∀ (α : Type) (nested : Contract α) (pre : ContractState),
    (behavioralOneLevelCallback 2 nested).run pre =
      ContractResult.revert "HOST_CALLBACK_LEVEL_EXCEEDED" pre

/-- When the actual nested execution reverts, bind skips the arbitrary resume and
top-level `Contract.run` restores `pre` (`Verity/Core.lean:291-301`). -/
def failedNestedRollsBackAndPreventsResume {α β γ : Type}
    (outerPrefix : Contract α) (nested : α → Contract β)
    (outerResume : α → β → Contract γ) : Prop :=
  ∀ pre mid prefixValue msg,
    outerPrefix.run pre = ContractResult.success prefixValue mid →
    (nested prefixValue).run mid = ContractResult.revert msg mid →
    (runOneLevelOuterNested outerPrefix nested outerResume).run pre =
      ContractResult.revert msg pre

/-- Public decoded CREATE_FLOW execution for a non-app receiver. -/
def runCreateNonApp
    (s : ContractState) (sender receiver : Address)
    (flowRate liquidationPeriod minimumDeposit timestamp : Uint256) : ContractResult Unit :=
  (SuperfluidCFA.createFlowNonApp
    sender receiver flowRate liquidationPeriod minimumDeposit timestamp).run s

/-- Public decoded UPDATE_FLOW execution for a non-app receiver. -/
def runUpdateNonApp
    (s : ContractState) (sender receiver : Address)
    (flowRate liquidationPeriod minimumDeposit timestamp : Uint256) : ContractResult Unit :=
  (SuperfluidCFA.updateFlowNonApp
    sender receiver flowRate liquidationPeriod minimumDeposit timestamp).run s

/-- Public decoded sender-initiated noncritical DELETE_FLOW execution. -/
def runDeleteNonApp
    (s : ContractState) (sender receiver : Address)
    (timestamp : Uint256) : ContractResult Unit :=
  (SuperfluidCFA.deleteFlowNonAppBySender sender receiver timestamp).run s

/-- Pinned create-only SelfDeletingFlowTestApp schedule. -/
def runReceiverDeleteCallback
    (s : ContractState) (sender receiver : Address)
    (flowRate liquidationPeriod minimumDeposit timestamp : Uint256) : ContractResult Uint256 :=
  (SuperfluidCFA.createFlowToAppWithReceiverDeleteCallback
    sender receiver flowRate liquidationPeriod minimumDeposit timestamp).run s

/-- CREATE_FLOW conserves the endpoint CFA projection at the update boundary. -/
def createNonAppPreservesCfaProjection
    (source : PinnedSourceState) (s : ContractState) (sender receiver : Address)
    (flowRate liquidationPeriod minimumDeposit timestamp : Uint256) : Prop :=
  pinnedSourcePathRelation source s sender receiver timestamp →
  let result := runCreateNonApp s sender receiver flowRate liquidationPeriod minimumDeposit timestamp
  modelSucceeded result →
  sourcePostRelation source result.snd sender receiver ∧
  pairCfaProjectionAt result.snd sender receiver timestamp =
    pairCfaProjectionAt s sender receiver timestamp

/-- CREATE_FLOW applies opposite endpoint rate deltas. -/
def createNonAppPreservesPairNetFlowRate
    (source : PinnedSourceState) (s : ContractState) (sender receiver : Address)
    (flowRate liquidationPeriod minimumDeposit timestamp : Uint256) : Prop :=
  pinnedSourcePathRelation source s sender receiver timestamp →
  let result := runCreateNonApp s sender receiver flowRate liquidationPeriod minimumDeposit timestamp
  modelSucceeded result →
  sourcePostRelation source result.snd sender receiver ∧
  pairNetFlowRate result.snd sender receiver = pairNetFlowRate s sender receiver

/-- CREATE_FLOW frames every unrelated account projection field. -/
def createNonAppFramesUnrelatedAccount
    (source : PinnedSourceState) (s : ContractState) (sender receiver unrelated : Address)
    (flowRate liquidationPeriod minimumDeposit timestamp : Uint256) : Prop :=
  pinnedSourcePathRelation source s sender receiver timestamp →
  unrelated ≠ sender → unrelated ≠ receiver →
  let result := runCreateNonApp s sender receiver flowRate liquidationPeriod minimumDeposit timestamp
  modelSucceeded result →
  sourcePostRelation source result.snd sender receiver ∧
  result.snd.storageMap 0 unrelated = s.storageMap 0 unrelated ∧
  result.snd.storageMap 1 unrelated = s.storageMap 1 unrelated ∧
  result.snd.storageMap 2 unrelated = s.storageMap 2 unrelated ∧
  result.snd.storageMap 3 unrelated = s.storageMap 3 unrelated ∧
  result.snd.storageMap 4 unrelated = s.storageMap 4 unrelated

/-- UPDATE_FLOW conserves the endpoint CFA projection at the update boundary. -/
def updateNonAppPreservesCfaProjection
    (source : PinnedSourceState) (s : ContractState) (sender receiver : Address)
    (flowRate liquidationPeriod minimumDeposit timestamp : Uint256) : Prop :=
  pinnedSourcePathRelation source s sender receiver timestamp →
  let result := runUpdateNonApp s sender receiver flowRate liquidationPeriod minimumDeposit timestamp
  modelSucceeded result →
  sourcePostRelation source result.snd sender receiver ∧
  pairCfaProjectionAt result.snd sender receiver timestamp =
    pairCfaProjectionAt s sender receiver timestamp

/-- UPDATE_FLOW applies opposite endpoint rate deltas. -/
def updateNonAppPreservesPairNetFlowRate
    (source : PinnedSourceState) (s : ContractState) (sender receiver : Address)
    (flowRate liquidationPeriod minimumDeposit timestamp : Uint256) : Prop :=
  pinnedSourcePathRelation source s sender receiver timestamp →
  let result := runUpdateNonApp s sender receiver flowRate liquidationPeriod minimumDeposit timestamp
  modelSucceeded result →
  sourcePostRelation source result.snd sender receiver ∧
  pairNetFlowRate result.snd sender receiver = pairNetFlowRate s sender receiver

/-- UPDATE_FLOW frames every unrelated account projection field. -/
def updateNonAppFramesUnrelatedAccount
    (source : PinnedSourceState) (s : ContractState) (sender receiver unrelated : Address)
    (flowRate liquidationPeriod minimumDeposit timestamp : Uint256) : Prop :=
  pinnedSourcePathRelation source s sender receiver timestamp →
  unrelated ≠ sender → unrelated ≠ receiver →
  let result := runUpdateNonApp s sender receiver flowRate liquidationPeriod minimumDeposit timestamp
  modelSucceeded result →
  sourcePostRelation source result.snd sender receiver ∧
  result.snd.storageMap 0 unrelated = s.storageMap 0 unrelated ∧
  result.snd.storageMap 1 unrelated = s.storageMap 1 unrelated ∧
  result.snd.storageMap 2 unrelated = s.storageMap 2 unrelated ∧
  result.snd.storageMap 3 unrelated = s.storageMap 3 unrelated ∧
  result.snd.storageMap 4 unrelated = s.storageMap 4 unrelated

/-- Noncritical sender DELETE_FLOW conserves the endpoint CFA projection. -/
def deleteNonAppPreservesCfaProjection
    (source : PinnedSourceState) (s : ContractState) (sender receiver : Address) (timestamp : Uint256) : Prop :=
  pinnedSourcePathRelation source s sender receiver timestamp →
  let result := runDeleteNonApp s sender receiver timestamp
  modelSucceeded result →
  sourcePostRelation source result.snd sender receiver ∧
  pairCfaProjectionAt result.snd sender receiver timestamp =
    pairCfaProjectionAt s sender receiver timestamp

/-- Noncritical sender DELETE_FLOW applies opposite endpoint rate deltas. -/
def deleteNonAppPreservesPairNetFlowRate
    (source : PinnedSourceState) (s : ContractState) (sender receiver : Address) (timestamp : Uint256) : Prop :=
  pinnedSourcePathRelation source s sender receiver timestamp →
  let result := runDeleteNonApp s sender receiver timestamp
  modelSucceeded result →
  sourcePostRelation source result.snd sender receiver ∧
  pairNetFlowRate result.snd sender receiver = pairNetFlowRate s sender receiver

/-- Noncritical sender DELETE_FLOW frames every unrelated account projection field. -/
def deleteNonAppFramesUnrelatedAccount
    (source : PinnedSourceState) (s : ContractState) (sender receiver unrelated : Address) (timestamp : Uint256) : Prop :=
  pinnedSourcePathRelation source s sender receiver timestamp →
  unrelated ≠ sender → unrelated ≠ receiver →
  let result := runDeleteNonApp s sender receiver timestamp
  modelSucceeded result →
  sourcePostRelation source result.snd sender receiver ∧
  result.snd.storageMap 0 unrelated = s.storageMap 0 unrelated ∧
  result.snd.storageMap 1 unrelated = s.storageMap 1 unrelated ∧
  result.snd.storageMap 2 unrelated = s.storageMap 2 unrelated ∧
  result.snd.storageMap 3 unrelated = s.storageMap 3 unrelated ∧
  result.snd.storageMap 4 unrelated = s.storageMap 4 unrelated

/-- The source-pinned after-created callback reloads zero and leaves the pair deleted. -/
def receiverDeleteCallbackReloadsFinalZero
    (source : PinnedSourceState) (s : ContractState) (sender receiver : Address)
    (flowRate liquidationPeriod minimumDeposit timestamp : Uint256) : Prop :=
  pinnedSourcePathRelation source s sender receiver timestamp →
  let result := runReceiverDeleteCallback
    s sender receiver flowRate liquidationPeriod minimumDeposit timestamp
  modelSucceeded result →
  sourcePostRelation source result.snd sender receiver ∧
  result.getValue? = some 0 ∧
  storedFlowRate result.snd sender receiver = 0 ∧
  result.snd.storageMap2 9 sender receiver = 0

/-- The create-only receiver self-delete callback conserves the endpoint CFA projection. -/
def receiverDeleteCallbackPreservesCfaProjection
    (source : PinnedSourceState) (s : ContractState) (sender receiver : Address)
    (flowRate liquidationPeriod minimumDeposit timestamp : Uint256) : Prop :=
  pinnedSourcePathRelation source s sender receiver timestamp →
  let result := runReceiverDeleteCallback
    s sender receiver flowRate liquidationPeriod minimumDeposit timestamp
  modelSucceeded result →
  sourcePostRelation source result.snd sender receiver ∧
  pairCfaProjectionAt result.snd sender receiver timestamp =
    pairCfaProjectionAt s sender receiver timestamp

/-- The create-only receiver self-delete callback leaves the endpoint rate sum unchanged. -/
def receiverDeleteCallbackPreservesPairNetFlowRate
    (source : PinnedSourceState) (s : ContractState) (sender receiver : Address)
    (flowRate liquidationPeriod minimumDeposit timestamp : Uint256) : Prop :=
  pinnedSourcePathRelation source s sender receiver timestamp →
  let result := runReceiverDeleteCallback
    s sender receiver flowRate liquidationPeriod minimumDeposit timestamp
  modelSucceeded result →
  sourcePostRelation source result.snd sender receiver ∧
  pairNetFlowRate result.snd sender receiver = pairNetFlowRate s sender receiver

/-- The callback schedule frames every unrelated account projection field. -/
def receiverDeleteCallbackFramesUnrelatedAccount
    (source : PinnedSourceState) (s : ContractState) (sender receiver unrelated : Address)
    (flowRate liquidationPeriod minimumDeposit timestamp : Uint256) : Prop :=
  pinnedSourcePathRelation source s sender receiver timestamp →
  unrelated ≠ sender → unrelated ≠ receiver →
  let result := runReceiverDeleteCallback
    s sender receiver flowRate liquidationPeriod minimumDeposit timestamp
  modelSucceeded result →
  sourcePostRelation source result.snd sender receiver ∧
  result.snd.storageMap 0 unrelated = s.storageMap 0 unrelated ∧
  result.snd.storageMap 1 unrelated = s.storageMap 1 unrelated ∧
  result.snd.storageMap 2 unrelated = s.storageMap 2 unrelated ∧
  result.snd.storageMap 3 unrelated = s.storageMap 3 unrelated ∧
  result.snd.storageMap 4 unrelated = s.storageMap 4 unrelated

/-! Small executable mutation witnesses for the finite-universe and callback hypotheses. -/

def regressionSender : Address := 1
def regressionReceiver : Address := 2
def regressionUnrelated : Address := 3
def regressionNegOne : Uint256 := sub 0 1

def finiteProjectionRegressionPost (corruptUnrelated : Bool) : ContractState :=
  { defaultState with storageMap := fun slotIndex account =>
      if slotIndex == 0 && account == regressionSender then regressionNegOne
      else if slotIndex == 0 && account == regressionReceiver then 1
      else if corruptUnrelated && slotIndex == 0 && account == regressionUnrelated then 1
      else 0 }

/-- W1-W3: endpoint cancellation alone does not survive a missing sender, a corrupt
unrelated member, or duplicate counting. -/
theorem finiteUniverseHypothesesRegressionWitnesses :
    pairCfaProjectionAt (finiteProjectionRegressionPost false)
        regressionSender regressionReceiver 0 =
      pairCfaProjectionAt defaultState regressionSender regressionReceiver 0 ∧
    modularCfaGlobalProjectionSumAt (finiteProjectionRegressionPost false)
        [regressionReceiver, regressionUnrelated] 0 ≠
      modularCfaGlobalProjectionSumAt defaultState
        [regressionReceiver, regressionUnrelated] 0 ∧
    modularCfaGlobalProjectionSumAt (finiteProjectionRegressionPost true)
        [regressionSender, regressionReceiver, regressionUnrelated] 0 ≠
      modularCfaGlobalProjectionSumAt defaultState
        [regressionSender, regressionReceiver, regressionUnrelated] 0 ∧
    modularCfaGlobalProjectionSumAt (finiteProjectionRegressionPost false)
        [regressionSender, regressionSender, regressionReceiver] 0 ≠
      modularCfaGlobalProjectionSumAt defaultState
        [regressionSender, regressionSender, regressionReceiver] 0 := by
  decide

def nestedCorruptionWitnessProgram : Contract Unit :=
  runOneLevelOuterNested
    (Verity.pure ())
    (fun _ => setMapping SuperfluidCFA.sharedSettledBalances regressionUnrelated 1)
    (fun _ _ => Verity.pure ())

/-- W4: a successful level-1 nested Contract can corrupt an unrelated account, so its
independent preservation/frame obligation is necessary for the composition theorem. -/
theorem nestedCorruptionNeedsComponentObligation :
    let result := nestedCorruptionWitnessProgram.run defaultState
    result.isSuccess = true ∧
    modularCfaGlobalProjectionSumAt result.snd
      [regressionSender, regressionReceiver, regressionUnrelated] 0 = 1 := by
  decide

/-- The modeled operation-time scope includes both uint32 endpoints and excludes the
first word past the boundary. -/
theorem inclusiveUint32TimestampBoundaryWitness :
    (0 : Uint256) ≤ UINT32_MAX_WORD ∧
    UINT32_MAX_WORD ≤ UINT32_MAX_WORD ∧
    ¬((4294967296 : Uint256) ≤ UINT32_MAX_WORD) := by
  decide

/-!
The following four operation properties deliberately quantify every observation word
`tau` with `operationTimestamp ≤ tau`. Their conclusions are equalities in EVM-word
arithmetic modulo `2^256`; they do not assert unbounded integer balance, native
multi-agreement `realtimeBalanceOf`, total supply, or full-protocol conservation.
`operationTimestamp ≤ UINT32_MAX_WORD` is inclusive and exposes the model's source
packing boundary, while `tau` need not itself be packed into CFA storage.
-/

/-- Successful non-app CREATE_FLOW preserves the fixed finite modular CFA sum at every
observation time at or after its inclusive uint32-scoped operation timestamp. -/
def createNonAppPreservesFutureModularCfaGlobalProjection
    (source : PinnedSourceState) (s : ContractState) (accounts : List Address)
    (sender receiver : Address)
    (flowRate liquidationPeriod minimumDeposit operationTimestamp tau : Uint256) : Prop :=
  CfaPairCoveredBy accounts sender receiver →
  operationTimestamp ≤ UINT32_MAX_WORD →
  operationTimestamp ≤ tau →
  pinnedSourcePathRelation source s sender receiver operationTimestamp →
  let result := runCreateNonApp s sender receiver flowRate liquidationPeriod
    minimumDeposit operationTimestamp
  modelSucceeded result →
  sourcePostRelation source result.snd sender receiver ∧
  modularCfaGlobalProjectionSumAt result.snd accounts tau =
    modularCfaGlobalProjectionSumAt s accounts tau

/-- Successful non-app UPDATE_FLOW preserves the fixed finite modular CFA sum at every
observation time at or after its inclusive uint32-scoped operation timestamp. -/
def updateNonAppPreservesFutureModularCfaGlobalProjection
    (source : PinnedSourceState) (s : ContractState) (accounts : List Address)
    (sender receiver : Address)
    (flowRate liquidationPeriod minimumDeposit operationTimestamp tau : Uint256) : Prop :=
  CfaPairCoveredBy accounts sender receiver →
  operationTimestamp ≤ UINT32_MAX_WORD →
  operationTimestamp ≤ tau →
  pinnedSourcePathRelation source s sender receiver operationTimestamp →
  let result := runUpdateNonApp s sender receiver flowRate liquidationPeriod
    minimumDeposit operationTimestamp
  modelSucceeded result →
  sourcePostRelation source result.snd sender receiver ∧
  modularCfaGlobalProjectionSumAt result.snd accounts tau =
    modularCfaGlobalProjectionSumAt s accounts tau

/-- Successful sender-initiated noncritical DELETE_FLOW preserves the fixed finite
modular CFA sum at every observation time at or after the operation timestamp. -/
def deleteNonAppPreservesFutureModularCfaGlobalProjection
    (source : PinnedSourceState) (s : ContractState) (accounts : List Address)
    (sender receiver : Address) (operationTimestamp tau : Uint256) : Prop :=
  CfaPairCoveredBy accounts sender receiver →
  operationTimestamp ≤ UINT32_MAX_WORD →
  operationTimestamp ≤ tau →
  pinnedSourcePathRelation source s sender receiver operationTimestamp →
  let result := runDeleteNonApp s sender receiver operationTimestamp
  modelSucceeded result →
  sourcePostRelation source result.snd sender receiver ∧
  modularCfaGlobalProjectionSumAt result.snd accounts tau =
    modularCfaGlobalProjectionSumAt s accounts tau

/-- The concrete source-pinned one-level receiver self-delete preserves the fixed finite
modular CFA sum at every later observation time. Its actor/app/token/context, registry,
noop, jailed, credit, and selected same-flow no-callback guards remain explicit here;
the generic hook itself does not claim to validate the complete Host ABI/context. -/
def receiverDeleteCallbackPreservesFutureModularCfaGlobalProjection
    (source : PinnedSourceState) (s : ContractState) (accounts : List Address)
    (sender receiver : Address)
    (flowRate liquidationPeriod minimumDeposit operationTimestamp tau : Uint256) : Prop :=
  CfaPairCoveredBy accounts sender receiver →
  operationTimestamp ≤ UINT32_MAX_WORD →
  operationTimestamp ≤ tau →
  pinnedSourcePathRelation source s sender receiver operationTimestamp →
  ConcreteSelfDeletingCallbackGuards source sender receiver flowRate liquidationPeriod
    minimumDeposit →
  let result := runReceiverDeleteCallback s sender receiver flowRate liquidationPeriod
    minimumDeposit operationTimestamp
  modelSucceeded result →
  sourcePostRelation source result.snd sender receiver ∧
  modularCfaGlobalProjectionSumAt result.snd accounts tau =
    modularCfaGlobalProjectionSumAt s accounts tau

/-- Concrete-instantiation behavior. Successful execution derives all retained source
bindings and is exactly the factored runner whose nested component deletes the original
`(sender, receiver)` pair at the original timestamp before the outer reload resumes. -/
def receiverDeleteCallbackFactoredInstanceBehavior
    (source : PinnedSourceState) (s : ContractState) (sender receiver : Address)
    (flowRate liquidationPeriod minimumDeposit operationTimestamp : Uint256) : Prop :=
  operationTimestamp ≤ UINT32_MAX_WORD →
  pinnedSourcePathRelation source s sender receiver operationTimestamp →
  let result := runReceiverDeleteCallback s sender receiver flowRate liquidationPeriod
    minimumDeposit operationTimestamp
  modelSucceeded result →
  ConcreteSelfDeletingCallbackGuards source sender receiver flowRate liquidationPeriod
      minimumDeposit ∧
  sourcePostRelation source result.snd sender receiver ∧
  result =
    (runOneLevelOuterNested
      (SuperfluidCFA._receiverDeleteCallbackOuterPrefix sender receiver flowRate
        liquidationPeriod minimumDeposit operationTimestamp)
      (fun _ => SuperfluidCFA._receiverDeleteCallbackNestedDelete sender receiver
        operationTimestamp)
      (fun _ _ => SuperfluidCFA._receiverDeleteCallbackOuterResume sender receiver
        operationTimestamp)).run s ∧
  result.getValue? = some (storedFlowRate result.snd sender receiver)

end Benchmark.Cases.Superfluid.RealtimeBalanceConservation
