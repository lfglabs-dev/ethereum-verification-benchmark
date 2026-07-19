import Benchmark.Cases.Enzyme.OnyxFeeHandler.Contract

namespace Benchmark.Cases.Enzyme.OnyxFeeHandler

open Verity
open Verity.EVM.Uint256
open Verity.Stdlib.Math

def totalFeesOwedOf (s : ContractState) : Uint256 :=
  s.storage FeeHandler.totalFeesOwed.slot

def feesOwedTo (s : ContractState) (recipient : Address) : Uint256 :=
  s.storageMap FeeHandler.userFeesOwed.slot recipient

def managementFeeTrackerOf (s : ContractState) : Address :=
  s.storageAddr FeeHandler.managementFeeTracker.slot

def performanceFeeTrackerOf (s : ContractState) : Address :=
  s.storageAddr FeeHandler.performanceFeeTracker.slot

def managementFeeRecipientOf (s : ContractState) : Address :=
  s.storageAddr FeeHandler.managementFeeRecipient.slot

def performanceFeeRecipientOf (s : ContractState) : Address :=
  s.storageAddr FeeHandler.performanceFeeRecipient.slot

def valuationHandlerCallSucceeds (env : Verity.Env) (shares : Address) : Prop :=
  externalCallSucceeded env shares getValuationHandlerSelector [] = true

def valuationHandlerWord (env : Verity.Env) (shares : Address) : Uint256 :=
  externalCallReturndata env shares getValuationHandlerSelector []

/-- The exact net-value argument passed to the management tracker. -/
def managementFeeBase (s : ContractState) (totalPositionsValue : Uint256) : Uint256 :=
  sub totalPositionsValue (totalFeesOwedOf s)

def managementFeeCallSucceeds
    (env : Verity.Env) (s : ContractState) (totalPositionsValue : Uint256) : Prop :=
  externalCallSucceeded env (managementFeeTrackerOf s) settleManagementFeeSelector
    [managementFeeBase s totalPositionsValue] = true

/-- Arbitrary management amount returned by the environment for the exact call. -/
def managementFeeAmount
    (env : Verity.Env) (s : ContractState) (totalPositionsValue : Uint256) : Uint256 :=
  externalCallReturndata env (managementFeeTrackerOf s) settleManagementFeeSelector
    [managementFeeBase s totalPositionsValue]

def totalFeesOwedAfterManagement
    (env : Verity.Env) (s : ContractState) (totalPositionsValue : Uint256) : Uint256 :=
  add (totalFeesOwedOf s) (managementFeeAmount env s totalPositionsValue)

def feesOwedAfterManagement
    (env : Verity.Env)
    (s : ContractState)
    (totalPositionsValue : Uint256)
    (user : Address) : Uint256 :=
  if user = managementFeeRecipientOf s then
    add (feesOwedTo s user) (managementFeeAmount env s totalPositionsValue)
  else
    feesOwedTo s user

/-- The exact net-value argument passed to the performance tracker. -/
def performanceFeeBase
    (env : Verity.Env) (s : ContractState) (totalPositionsValue : Uint256) : Uint256 :=
  sub (managementFeeBase s totalPositionsValue)
    (managementFeeAmount env s totalPositionsValue)

def performanceFeeCallSucceeds
    (env : Verity.Env) (s : ContractState) (totalPositionsValue : Uint256) : Prop :=
  externalCallSucceeded env (performanceFeeTrackerOf s) settlePerformanceFeeSelector
    [performanceFeeBase env s totalPositionsValue] = true

/-- Arbitrary performance amount returned by the environment for the exact call. -/
def performanceFeeAmount
    (env : Verity.Env) (s : ContractState) (totalPositionsValue : Uint256) : Uint256 :=
  externalCallReturndata env (performanceFeeTrackerOf s) settlePerformanceFeeSelector
    [performanceFeeBase env s totalPositionsValue]

def expectedFeesOwedAfterDynamicSettlement
    (env : Verity.Env)
    (s : ContractState)
    (totalPositionsValue : Uint256)
    (user : Address) : Uint256 :=
  let afterManagement := feesOwedAfterManagement env s totalPositionsValue user
  if user = performanceFeeRecipientOf s then
    add afterManagement (performanceFeeAmount env s totalPositionsValue)
  else
    afterManagement

/--
Frame for the modeled EVM storage projections. The transition may change only
the aggregate liability slot and the address-keyed liability mapping slot.
Verity's `knownAddresses` proof-bookkeeping field is intentionally outside this
frame because `setMapping` updates it when recording written mapping keys.
-/
def feeHandlerStorageFrame (s s' : ContractState) : Prop :=
  s'.storageAddr = s.storageAddr ∧
  (∀ storageSlot,
    storageSlot ≠ FeeHandler.totalFeesOwed.slot →
      s'.storage storageSlot = s.storage storageSlot) ∧
  (∀ mappingSlot user,
    mappingSlot ≠ FeeHandler.userFeesOwed.slot →
      s'.storageMap mappingSlot user = s.storageMap mappingSlot user)

def managementOnlyExactSettlement
    (env : Verity.Env)
    (s s' : ContractState)
    (totalPositionsValue : Uint256) : Prop :=
  totalFeesOwedOf s' =
      add (totalFeesOwedOf s) (managementFeeAmount env s totalPositionsValue) ∧
  (∀ user,
    feesOwedTo s' user =
      if user = managementFeeRecipientOf s then
        add (feesOwedTo s user) (managementFeeAmount env s totalPositionsValue)
      else feesOwedTo s user) ∧
  feeHandlerStorageFrame s s'

def performanceOnlyFeeBase
    (s : ContractState) (totalPositionsValue : Uint256) : Uint256 :=
  managementFeeBase s totalPositionsValue

def performanceOnlyFeeAmount
    (env : Verity.Env)
    (s : ContractState)
    (totalPositionsValue : Uint256) : Uint256 :=
  externalCallReturndata env (performanceFeeTrackerOf s)
    settlePerformanceFeeSelector [performanceOnlyFeeBase s totalPositionsValue]

def performanceOnlyCallSucceeds
    (env : Verity.Env)
    (s : ContractState)
    (totalPositionsValue : Uint256) : Prop :=
  externalCallSucceeded env (performanceFeeTrackerOf s)
    settlePerformanceFeeSelector [performanceOnlyFeeBase s totalPositionsValue] = true

def performanceOnlyExactSettlement
    (env : Verity.Env)
    (s s' : ContractState)
    (totalPositionsValue : Uint256) : Prop :=
  totalFeesOwedOf s' =
      add (totalFeesOwedOf s) (performanceOnlyFeeAmount env s totalPositionsValue) ∧
  (∀ user,
    feesOwedTo s' user =
      if user = performanceFeeRecipientOf s then
        add (feesOwedTo s user) (performanceOnlyFeeAmount env s totalPositionsValue)
      else feesOwedTo s user) ∧
  feeHandlerStorageFrame s s'

/-- Exact accounting for the both-trackers-enabled successful environment path. -/
def exact_dynamic_fee_settlement
    (env : Verity.Env)
    (totalPositionsValue : Uint256)
    (s s' : ContractState) : Prop :=
  totalFeesOwedOf s' =
      add
        (add (totalFeesOwedOf s) (managementFeeAmount env s totalPositionsValue))
        (performanceFeeAmount env s totalPositionsValue) ∧
  (∀ user,
    feesOwedTo s' user =
      expectedFeesOwedAfterDynamicSettlement env s totalPositionsValue user) ∧
  feeHandlerStorageFrame s s'

end Benchmark.Cases.Enzyme.OnyxFeeHandler