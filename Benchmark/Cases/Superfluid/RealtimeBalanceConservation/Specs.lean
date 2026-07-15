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

end Benchmark.Cases.Superfluid.RealtimeBalanceConservation
