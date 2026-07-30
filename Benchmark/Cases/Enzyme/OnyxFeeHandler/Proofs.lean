import Benchmark.Cases.Enzyme.OnyxFeeHandler.Specs
import Verity.Core.Reentrancy
import Verity.Proofs.Stdlib.Automation
import Verity.Proofs.Stdlib.Math

namespace Benchmark.Cases.Enzyme.OnyxFeeHandler

open Verity
open Verity.EVM.Uint256
open Verity.Stdlib.Math
open Verity.Proofs.Stdlib.Math (safeAdd_some safeAdd_none)
open Verity.Core.Invariant
open Verity.Core.Reentrancy

set_option linter.unusedSimpArgs false

namespace DynamicFeeProjectionEq

theorem refl (s : ContractState) : DynamicFeeProjectionEq s s := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ => rfl⟩

theorem trans {a b c : ContractState}
    (hab : DynamicFeeProjectionEq a b)
    (hbc : DynamicFeeProjectionEq b c) : DynamicFeeProjectionEq a c := by
  exact
    ⟨hbc.managementFeeTracker.trans hab.managementFeeTracker,
      hbc.performanceFeeTracker.trans hab.performanceFeeTracker,
      hbc.managementFeeRecipient.trans hab.managementFeeRecipient,
      hbc.performanceFeeRecipient.trans hab.performanceFeeRecipient,
      hbc.totalFeesOwed.trans hab.totalFeesOwed,
      fun user => (hbc.userFeesOwed user).trans (hab.userFeesOwed user)⟩

end DynamicFeeProjectionEq

/-- A projection-framing callback preserves every baseline snapshot invariant. -/
theorem dynamicFeeReentryStable_preserves
    {adv : ContractState → ContractState}
    (hAdv : DynamicFeeReentryStable adv)
    (baseline : ContractState) :
    Preserves (dynamicFeeProjectionInvariant baseline) adv := by
  intro s hs
  exact hs.trans (hAdv s)

/-- Package any audited finite registry of projection-framing callbacks as a
    genuine Verity reentrancy specification. -/
def dynamicFeeReentrancySpec
    (baseline : ContractState)
    (entrypoints : List (ContractState → ContractState))
    (hEntrypoints : ∀ f, f ∈ entrypoints → DynamicFeeReentryStable f) :
    ReentrancySpec where
  Inv := dynamicFeeProjectionInvariant baseline
  entrypoints := entrypoints
  entrypoints_preserve := by
    intro f hf
    exact dynamicFeeReentryStable_preserves (hEntrypoints f hf) baseline

/-- Any finite schedule drawn from an audited projection-framing registry is a
    valid callback transformer for the settlement theorem below. -/
theorem registered_reentry_schedule_stable
    (entrypoints schedule : List (ContractState → ContractState))
    (hEntrypoints : ∀ f, f ∈ entrypoints → DynamicFeeReentryStable f)
    (hSchedule : ∀ f, f ∈ schedule → f ∈ entrypoints) :
    DynamicFeeReentryStable (runSeq schedule) := by
  intro s
  exact (dynamicFeeReentrancySpec s entrypoints hEntrypoints).schedule_preserves
    schedule hSchedule s (DynamicFeeProjectionEq.refl s)

/-- Explicitly discharge the settlement theorem's callback rely when the
    environment hook is a schedule drawn from an audited framing registry. -/
theorem env_reentry_stable_of_registered_schedule
    (env : Verity.Env)
    (entrypoints schedule : List (ContractState → ContractState))
    (hEntrypoints : ∀ f, f ∈ entrypoints → DynamicFeeReentryStable f)
    (hSchedule : ∀ f, f ∈ schedule → f ∈ entrypoints)
    (hEnvReentry : env.reenter = runSeq schedule) :
    DynamicFeeReentryStable env.reenter := by
  rw [hEnvReentry]
  exact registered_reentry_schedule_stable entrypoints schedule hEntrypoints hSchedule

/-- Raw storage equalities extracted once for proof automation. -/
theorem dynamicFeeReentryStable_raw
    {adv : ContractState → ContractState}
    (hAdv : DynamicFeeReentryStable adv) :
    (∀ s, (adv s).storageAddr FeeHandler.managementFeeTracker.slot =
      s.storageAddr FeeHandler.managementFeeTracker.slot) ∧
    (∀ s, (adv s).storageAddr FeeHandler.performanceFeeTracker.slot =
      s.storageAddr FeeHandler.performanceFeeTracker.slot) ∧
    (∀ s, (adv s).storageAddr FeeHandler.managementFeeRecipient.slot =
      s.storageAddr FeeHandler.managementFeeRecipient.slot) ∧
    (∀ s, (adv s).storageAddr FeeHandler.performanceFeeRecipient.slot =
      s.storageAddr FeeHandler.performanceFeeRecipient.slot) ∧
    (∀ s, (adv s).storage FeeHandler.totalFeesOwed.slot =
      s.storage FeeHandler.totalFeesOwed.slot) ∧
    (∀ s user, (adv s).storageMap FeeHandler.userFeesOwed.slot user =
      s.storageMap FeeHandler.userFeesOwed.slot user) := by
  constructor
  · intro s
    simpa [managementFeeTrackerOf] using (hAdv s).managementFeeTracker
  constructor
  · intro s
    simpa [performanceFeeTrackerOf] using (hAdv s).performanceFeeTracker
  constructor
  · intro s
    simpa [managementFeeRecipientOf] using (hAdv s).managementFeeRecipient
  constructor
  · intro s
    simpa [performanceFeeRecipientOf] using (hAdv s).performanceFeeRecipient
  constructor
  · intro s
    simpa [totalFeesOwedOf] using (hAdv s).totalFeesOwed
  · intro s user
    simpa [feesOwedTo] using (hAdv s).userFeesOwed user

/--
For every environment whose exact valuation and tracker calls succeed, both
enabled trackers update aggregate and per-recipient liabilities by exactly their
arbitrary oracle return words. Tracker callbacks may arbitrarily transform state
outside the six observed dynamic-fee projections. The theorem also proves
successful termination, the selected configuration frame, and the
shared-recipient alias case.
-/
theorem settleDynamicFeesGivenPositionsValue_exact_accounting
    (env : Verity.Env)
    (totalPositionsValue : Uint256)
    (shares : Address)
    (s : ContractState)
    (hReentry : DynamicFeeReentryStable env.reenter)
    (hValuationCall : valuationHandlerCallSucceeds env shares)
    (hCaller : s.sender = wordToAddress (valuationHandlerWord env shares))
    (hPositionsCoverPriorFees : totalFeesOwedOf s <= totalPositionsValue)
    (hManagementEnabled : managementFeeTrackerOf s ≠ zeroAddress)
    (hPerformanceEnabled : performanceFeeTrackerOf s ≠ zeroAddress)
    (hManagementCall : managementFeeCallSucceeds env s totalPositionsValue)
    (hPerformanceCall : performanceFeeCallSucceeds env s totalPositionsValue)
    (hManagementFitsNet :
      managementFeeAmount env s totalPositionsValue <= managementFeeBase s totalPositionsValue)
    (hManagementRecipientNoOverflow :
      (feesOwedTo s (managementFeeRecipientOf s) : Nat) +
        (managementFeeAmount env s totalPositionsValue : Nat) <= MAX_UINT256)
    (hManagementTotalNoOverflow :
      (totalFeesOwedOf s : Nat) +
        (managementFeeAmount env s totalPositionsValue : Nat) <= MAX_UINT256)
    (hPerformanceRecipientNoOverflow :
      (feesOwedAfterManagement env s totalPositionsValue (performanceFeeRecipientOf s) : Nat) +
        (performanceFeeAmount env s totalPositionsValue : Nat) <= MAX_UINT256)
    (hPerformanceTotalNoOverflow :
      (totalFeesOwedAfterManagement env s totalPositionsValue : Nat) +
        (performanceFeeAmount env s totalPositionsValue : Nat) <= MAX_UINT256) :
    ∃ s',
      FeeHandler.settleDynamicFeesGivenPositionsValue env totalPositionsValue shares s =
        ContractResult.success () s' ∧
      exact_dynamic_fee_settlement env totalPositionsValue s s' := by
  obtain ⟨hReentryManagementTracker, hReentryPerformanceTracker,
      hReentryManagementRecipient, hReentryPerformanceRecipient,
      hReentryTotal, hReentryUsers⟩ := dynamicFeeReentryStable_raw hReentry
  have hSafeManagementRecipient := safeAdd_some
    (feesOwedTo s (managementFeeRecipientOf s))
    (managementFeeAmount env s totalPositionsValue)
    hManagementRecipientNoOverflow
  have hSafeManagementTotal := safeAdd_some
    (totalFeesOwedOf s)
    (managementFeeAmount env s totalPositionsValue)
    hManagementTotalNoOverflow
  have hSafePerformanceRecipient := safeAdd_some
    (feesOwedAfterManagement env s totalPositionsValue (performanceFeeRecipientOf s))
    (performanceFeeAmount env s totalPositionsValue)
    hPerformanceRecipientNoOverflow
  have hSafePerformanceTotal := safeAdd_some
    (totalFeesOwedAfterManagement env s totalPositionsValue)
    (performanceFeeAmount env s totalPositionsValue)
    hPerformanceTotalNoOverflow
  have hSafeManagementRecipientRaw :
      safeAdd
          (s.storageMap FeeHandler.userFeesOwed.slot
            (s.storageAddr FeeHandler.managementFeeRecipient.slot))
          (managementFeeAmount env s totalPositionsValue) =
        some
          (add
            (s.storageMap FeeHandler.userFeesOwed.slot
              (s.storageAddr FeeHandler.managementFeeRecipient.slot))
            (managementFeeAmount env s totalPositionsValue)) := by
    simpa [feesOwedTo, managementFeeRecipientOf, HAdd.hAdd, Add.add] using
      hSafeManagementRecipient
  have hSafeManagementTotalRaw :
      safeAdd (s.storage FeeHandler.totalFeesOwed.slot)
          (managementFeeAmount env s totalPositionsValue) =
        some
          (add (s.storage FeeHandler.totalFeesOwed.slot)
            (managementFeeAmount env s totalPositionsValue)) := by
    simpa [totalFeesOwedOf, HAdd.hAdd, Add.add] using hSafeManagementTotal
  have hSafePerformanceTotalRaw :
      safeAdd
          (add (s.storage FeeHandler.totalFeesOwed.slot)
            (managementFeeAmount env s totalPositionsValue))
          (performanceFeeAmount env s totalPositionsValue) =
        some
          (add
            (add (s.storage FeeHandler.totalFeesOwed.slot)
              (managementFeeAmount env s totalPositionsValue))
            (performanceFeeAmount env s totalPositionsValue)) := by
    simpa [totalFeesOwedAfterManagement, totalFeesOwedOf,
      HAdd.hAdd, Add.add] using hSafePerformanceTotal
  have hValuationCallRaw :
      externalCallSucceeded env shares getValuationHandlerSelector [] = true := by
    simpa [valuationHandlerCallSucceeds] using hValuationCall
  have hManagementCallRaw :
      externalCallSucceeded env (s.storageAddr FeeHandler.managementFeeTracker.slot)
          settleManagementFeeSelector
          [sub totalPositionsValue (s.storage FeeHandler.totalFeesOwed.slot)] = true := by
    simpa [managementFeeCallSucceeds, managementFeeTrackerOf,
      managementFeeBase, totalFeesOwedOf] using hManagementCall
  have hPerformanceCallRaw :
      externalCallSucceeded env (s.storageAddr FeeHandler.performanceFeeTracker.slot)
          settlePerformanceFeeSelector
          [sub (sub totalPositionsValue (s.storage FeeHandler.totalFeesOwed.slot))
            (managementFeeAmount env s totalPositionsValue)] = true := by
    simpa [performanceFeeCallSucceeds, performanceFeeTrackerOf,
      performanceFeeBase, managementFeeBase, totalFeesOwedOf] using hPerformanceCall
  have hValuationOracleRaw :
      env.callOracle "externalCallSucceeded"
          (externalCallKeyWords shares getValuationHandlerSelector []) ≠ 0 := by
    intro hZero
    have h := hValuationCallRaw
    simp [externalCallSucceeded, hZero] at h
  have hManagementOracleRaw :
      env.callOracle "externalCallSucceeded"
          (externalCallKeyWords
            (s.storageAddr FeeHandler.managementFeeTracker.slot)
            settleManagementFeeSelector
            [sub totalPositionsValue (s.storage FeeHandler.totalFeesOwed.slot)]) ≠ 0 := by
    intro hZero
    have h := hManagementCallRaw
    simp [externalCallSucceeded, hZero] at h
  have hPerformanceOracleRaw :
      env.callOracle "externalCallSucceeded"
          (externalCallKeyWords
            (s.storageAddr FeeHandler.performanceFeeTracker.slot)
            settlePerformanceFeeSelector
            [sub (sub totalPositionsValue (s.storage FeeHandler.totalFeesOwed.slot))
              (managementFeeAmount env s totalPositionsValue)]) ≠ 0 := by
    intro hZero
    have h := hPerformanceCallRaw
    simp [externalCallSucceeded, hZero] at h
  have hCallerRaw :
      s.sender = wordToAddress
        (externalCallReturndata env shares getValuationHandlerSelector []) := by
    simpa [valuationHandlerWord] using hCaller
  have hPositionsRaw :
      (s.storage FeeHandler.totalFeesOwed.slot).val <= totalPositionsValue.val := by
    simpa [totalFeesOwedOf, Verity.Core.Uint256.le_def] using
      hPositionsCoverPriorFees
  have hManagementFitsRaw :
      (managementFeeAmount env s totalPositionsValue).val <=
        (sub totalPositionsValue (s.storage FeeHandler.totalFeesOwed.slot)).val := by
    simpa [managementFeeBase, totalFeesOwedOf, Verity.Core.Uint256.le_def] using
      hManagementFitsNet
  have hManagementEnabledRaw :
      s.storageAddr FeeHandler.managementFeeTracker.slot ≠ (0 : Address) := by
    simpa [managementFeeTrackerOf, zeroAddress] using hManagementEnabled
  have hPerformanceEnabledRaw :
      s.storageAddr FeeHandler.performanceFeeTracker.slot ≠ (0 : Address) := by
    simpa [performanceFeeTrackerOf, zeroAddress] using hPerformanceEnabled
  unfold managementFeeAmount at hManagementFitsRaw hPerformanceOracleRaw
  simp only [managementFeeTrackerOf, managementFeeBase,
    totalFeesOwedOf] at hManagementFitsRaw hPerformanceOracleRaw
  by_cases hSameRecipient :
      managementFeeRecipientOf s = performanceFeeRecipientOf s
  · have hSameRecipientRaw :
        s.storageAddr FeeHandler.managementFeeRecipient.slot =
          s.storageAddr FeeHandler.performanceFeeRecipient.slot := by
      simpa [managementFeeRecipientOf, performanceFeeRecipientOf] using hSameRecipient
    have hSafePerformanceRecipientRaw :
        safeAdd
            (add
              (s.storageMap FeeHandler.userFeesOwed.slot
                (s.storageAddr FeeHandler.performanceFeeRecipient.slot))
              (managementFeeAmount env s totalPositionsValue))
            (performanceFeeAmount env s totalPositionsValue) =
          some
            (add
              (add
                (s.storageMap FeeHandler.userFeesOwed.slot
                  (s.storageAddr FeeHandler.performanceFeeRecipient.slot))
                (managementFeeAmount env s totalPositionsValue))
              (performanceFeeAmount env s totalPositionsValue)) := by
      simpa [feesOwedAfterManagement, feesOwedTo,
        managementFeeRecipientOf, performanceFeeRecipientOf,
        hSameRecipientRaw, HAdd.hAdd, Add.add] using hSafePerformanceRecipient
    have hSafeManagementRecipientSame :
        safeAdd
            (s.storageMap FeeHandler.userFeesOwed.slot
              (s.storageAddr FeeHandler.performanceFeeRecipient.slot))
            (managementFeeAmount env s totalPositionsValue) =
          some
            (add
              (s.storageMap FeeHandler.userFeesOwed.slot
                (s.storageAddr FeeHandler.performanceFeeRecipient.slot))
              (managementFeeAmount env s totalPositionsValue)) := by
      simpa [hSameRecipientRaw] using hSafeManagementRecipientRaw
    unfold managementFeeAmount at hSafeManagementRecipientSame hSafeManagementTotalRaw hSafePerformanceRecipientRaw hSafePerformanceTotalRaw
    unfold performanceFeeAmount at hSafePerformanceRecipientRaw hSafePerformanceTotalRaw
    unfold performanceFeeBase at hSafePerformanceRecipientRaw hSafePerformanceTotalRaw
    unfold managementFeeAmount at hSafePerformanceRecipientRaw hSafePerformanceTotalRaw
    simp only [managementFeeTrackerOf, performanceFeeTrackerOf, managementFeeBase, performanceFeeBase, totalFeesOwedOf] at hSafeManagementRecipientSame hSafeManagementTotalRaw hSafePerformanceRecipientRaw hSafePerformanceTotalRaw
    simp [exact_dynamic_fee_settlement, feeHandlerStorageFrame,
      expectedFeesOwedAfterDynamicSettlement, feesOwedAfterManagement,
      totalFeesOwedAfterManagement,
      FeeHandler.settleDynamicFeesGivenPositionsValue,
      FeeHandler.__increaseValueOwed, FeeHandler.__updateValueOwed,
      runStaticWordCall, runExternalWordCall,
      valuationHandlerCallSucceeds, valuationHandlerWord,
      managementFeeCallSucceeds, performanceFeeCallSucceeds,
      externalCallSucceeded,
      totalFeesOwedOf, feesOwedTo,
      managementFeeTrackerOf, performanceFeeTrackerOf,
      managementFeeRecipientOf, performanceFeeRecipientOf,
      managementFeeBase, managementFeeAmount,
      performanceFeeBase, performanceFeeAmount,
      hReentryManagementTracker, hReentryPerformanceTracker,
      hReentryManagementRecipient, hReentryPerformanceRecipient,
      hReentryTotal, hReentryUsers,
      hValuationOracleRaw, hManagementOracleRaw, hPerformanceOracleRaw,
      hCallerRaw, hPositionsRaw, hManagementEnabledRaw, hPerformanceEnabledRaw,
      hManagementFitsRaw, hSafeManagementRecipientSame, hSafeManagementTotalRaw,
      hSafePerformanceRecipientRaw, hSafePerformanceTotalRaw,
      hSameRecipient, hSameRecipientRaw,
      getStorage, getStorageAddr, getMapping, setStorage, setMapping, msgSender,
      requireSomeUint, Verity.require, Verity.bind, Bind.bind,
      Verity.pure, Pure.pure,
      ContractState.readSlot, ContractState.readAddrSlot, ContractState.readMap,
      ContractState.writeSlot, ContractState.writeMap,
      HAdd.hAdd, Add.add, beq_iff_eq, decide_eq_true_eq]
    intro user
    by_cases hUserRecipient :
        user = s.storageAddr FeeHandler.performanceFeeRecipient.slot
    · simp [hUserRecipient]
    · simp [hUserRecipient]
  · have hDifferentRecipientRaw :
        s.storageAddr FeeHandler.managementFeeRecipient.slot ≠
          s.storageAddr FeeHandler.performanceFeeRecipient.slot := by
      simpa [managementFeeRecipientOf, performanceFeeRecipientOf] using hSameRecipient
    have hDifferentRecipientRawSymm :
        s.storageAddr FeeHandler.performanceFeeRecipient.slot ≠
          s.storageAddr FeeHandler.managementFeeRecipient.slot :=
      Ne.symm hDifferentRecipientRaw
    have hSafePerformanceRecipientRaw :
        safeAdd
            (s.storageMap FeeHandler.userFeesOwed.slot
              (s.storageAddr FeeHandler.performanceFeeRecipient.slot))
            (performanceFeeAmount env s totalPositionsValue) =
          some
            (add
              (s.storageMap FeeHandler.userFeesOwed.slot
                (s.storageAddr FeeHandler.performanceFeeRecipient.slot))
              (performanceFeeAmount env s totalPositionsValue)) := by
      simpa [feesOwedAfterManagement, feesOwedTo,
        managementFeeRecipientOf, performanceFeeRecipientOf,
        hDifferentRecipientRaw, hDifferentRecipientRawSymm,
        HAdd.hAdd, Add.add] using hSafePerformanceRecipient
    unfold managementFeeAmount at hSafeManagementRecipientRaw hSafeManagementTotalRaw hSafePerformanceRecipientRaw hSafePerformanceTotalRaw
    unfold performanceFeeAmount at hSafePerformanceRecipientRaw hSafePerformanceTotalRaw
    unfold performanceFeeBase at hSafePerformanceRecipientRaw hSafePerformanceTotalRaw
    unfold managementFeeAmount at hSafePerformanceRecipientRaw hSafePerformanceTotalRaw
    simp only [managementFeeTrackerOf, performanceFeeTrackerOf, managementFeeBase, performanceFeeBase, totalFeesOwedOf] at hSafeManagementRecipientRaw hSafeManagementTotalRaw hSafePerformanceRecipientRaw hSafePerformanceTotalRaw
    simp [exact_dynamic_fee_settlement, feeHandlerStorageFrame,
      expectedFeesOwedAfterDynamicSettlement, feesOwedAfterManagement,
      totalFeesOwedAfterManagement,
      FeeHandler.settleDynamicFeesGivenPositionsValue,
      FeeHandler.__increaseValueOwed, FeeHandler.__updateValueOwed,
      runStaticWordCall, runExternalWordCall,
      valuationHandlerCallSucceeds, valuationHandlerWord,
      managementFeeCallSucceeds, performanceFeeCallSucceeds,
      externalCallSucceeded,
      totalFeesOwedOf, feesOwedTo,
      managementFeeTrackerOf, performanceFeeTrackerOf,
      managementFeeRecipientOf, performanceFeeRecipientOf,
      managementFeeBase, managementFeeAmount,
      performanceFeeBase, performanceFeeAmount,
      hReentryManagementTracker, hReentryPerformanceTracker,
      hReentryManagementRecipient, hReentryPerformanceRecipient,
      hReentryTotal, hReentryUsers,
      hValuationOracleRaw, hManagementOracleRaw, hPerformanceOracleRaw,
      hCallerRaw, hPositionsRaw, hManagementEnabledRaw, hPerformanceEnabledRaw,
      hManagementFitsRaw, hSafeManagementRecipientRaw, hSafeManagementTotalRaw,
      hSafePerformanceRecipientRaw, hSafePerformanceTotalRaw,
      hSameRecipient, hDifferentRecipientRaw, hDifferentRecipientRawSymm,
      getStorage, getStorageAddr, getMapping, setStorage, setMapping, msgSender,
      requireSomeUint, Verity.require, Verity.bind, Bind.bind,
      Verity.pure, Pure.pure,
      ContractState.readSlot, ContractState.readAddrSlot, ContractState.readMap,
      ContractState.writeSlot, ContractState.writeMap,
      HAdd.hAdd, Add.add, beq_iff_eq, decide_eq_true_eq]
    intro user
    by_cases hPerformanceRecipient :
        user = s.storageAddr FeeHandler.performanceFeeRecipient.slot
    · simp [hPerformanceRecipient, hDifferentRecipientRawSymm]
    · by_cases hManagementRecipient :
          user = s.storageAddr FeeHandler.managementFeeRecipient.slot
      · simp [hPerformanceRecipient, hManagementRecipient, hDifferentRecipientRaw]
      · simp [hPerformanceRecipient, hManagementRecipient, hDifferentRecipientRaw]

theorem management_only_exact_accounting
    (env : Verity.Env)
    (totalPositionsValue : Uint256)
    (shares : Address)
    (s : ContractState)
    (hReentry : DynamicFeeReentryStable env.reenter)
    (hValuationCall : valuationHandlerCallSucceeds env shares)
    (hCaller : s.sender = wordToAddress (valuationHandlerWord env shares))
    (hPositionsCoverPriorFees : totalFeesOwedOf s ≤ totalPositionsValue)
    (hManagementEnabled : managementFeeTrackerOf s ≠ zeroAddress)
    (hPerformanceDisabled : performanceFeeTrackerOf s = zeroAddress)
    (hManagementCall : managementFeeCallSucceeds env s totalPositionsValue)
    (hManagementRecipientNoOverflow :
      (feesOwedTo s (managementFeeRecipientOf s)).val +
        (managementFeeAmount env s totalPositionsValue).val ≤ MAX_UINT256)
    (hManagementTotalNoOverflow :
      (totalFeesOwedOf s).val +
        (managementFeeAmount env s totalPositionsValue).val ≤ MAX_UINT256) :
    ∃ s',
      FeeHandler.settleDynamicFeesGivenPositionsValue env totalPositionsValue shares s =
        ContractResult.success () s' ∧
      managementOnlyExactSettlement env s s' totalPositionsValue := by
  obtain ⟨hReentryManagementTracker, hReentryPerformanceTracker,
      hReentryManagementRecipient, hReentryPerformanceRecipient,
      hReentryTotal, hReentryUsers⟩ := dynamicFeeReentryStable_raw hReentry
  have hSafeRecipient := safeAdd_some
    (feesOwedTo s (managementFeeRecipientOf s))
    (managementFeeAmount env s totalPositionsValue)
    hManagementRecipientNoOverflow
  have hSafeTotal := safeAdd_some
    (totalFeesOwedOf s)
    (managementFeeAmount env s totalPositionsValue)
    hManagementTotalNoOverflow
  have hSafeRecipientRaw :
      safeAdd
          (s.storageMap FeeHandler.userFeesOwed.slot
            (s.storageAddr FeeHandler.managementFeeRecipient.slot))
          (managementFeeAmount env s totalPositionsValue) =
        some
          (add
            (s.storageMap FeeHandler.userFeesOwed.slot
              (s.storageAddr FeeHandler.managementFeeRecipient.slot))
            (managementFeeAmount env s totalPositionsValue)) := by
    simpa [feesOwedTo, managementFeeRecipientOf, HAdd.hAdd, Add.add] using hSafeRecipient
  have hSafeTotalRaw :
      safeAdd (s.storage FeeHandler.totalFeesOwed.slot)
          (managementFeeAmount env s totalPositionsValue) =
        some
          (add (s.storage FeeHandler.totalFeesOwed.slot)
            (managementFeeAmount env s totalPositionsValue)) := by
    simpa [totalFeesOwedOf, HAdd.hAdd, Add.add] using hSafeTotal
  have hValuationOracle :
      env.callOracle "externalCallSucceeded"
          (externalCallKeyWords shares getValuationHandlerSelector []) ≠ 0 := by
    intro hZero
    have h := hValuationCall
    simp [valuationHandlerCallSucceeds, externalCallSucceeded, hZero] at h
  have hManagementOracle :
      env.callOracle "externalCallSucceeded"
          (externalCallKeyWords (managementFeeTrackerOf s) settleManagementFeeSelector
            [managementFeeBase s totalPositionsValue]) ≠ 0 := by
    intro hZero
    have h := hManagementCall
    simp [managementFeeCallSucceeds, externalCallSucceeded, hZero] at h
  have hPositionsRaw :
      (s.storage FeeHandler.totalFeesOwed.slot).val ≤ totalPositionsValue.val := by
    simpa [totalFeesOwedOf, Verity.Core.Uint256.le_def] using hPositionsCoverPriorFees
  have hManagementEnabledRaw :
      s.storageAddr FeeHandler.managementFeeTracker.slot ≠ (0 : Address) := by
    simpa [managementFeeTrackerOf, zeroAddress] using hManagementEnabled
  have hPerformanceDisabledRaw :
      s.storageAddr FeeHandler.performanceFeeTracker.slot = (0 : Address) := by
    simpa [performanceFeeTrackerOf, zeroAddress] using hPerformanceDisabled
  have hCallerRaw :
      s.sender = wordToAddress
        (externalCallReturndata env shares getValuationHandlerSelector []) := by
    simpa [valuationHandlerWord] using hCaller
  unfold managementFeeAmount at hSafeRecipientRaw hSafeTotalRaw
  simp only [managementFeeTrackerOf, managementFeeBase, totalFeesOwedOf] at hSafeRecipientRaw hSafeTotalRaw hManagementOracle
  simp [managementOnlyExactSettlement, feeHandlerStorageFrame,
    FeeHandler.settleDynamicFeesGivenPositionsValue,
    FeeHandler.__increaseValueOwed, FeeHandler.__updateValueOwed,
    runStaticWordCall, runExternalWordCall, externalCallSucceeded,
    totalFeesOwedOf, feesOwedTo,
    managementFeeTrackerOf, performanceFeeTrackerOf, managementFeeRecipientOf,
    managementFeeBase, managementFeeAmount,
    hReentryManagementTracker, hReentryPerformanceTracker,
    hReentryManagementRecipient, hReentryPerformanceRecipient,
    hReentryTotal, hReentryUsers,
    hValuationOracle, hManagementOracle,
    hPositionsRaw, hManagementEnabledRaw, hPerformanceDisabledRaw, hCallerRaw,
    hSafeRecipientRaw, hSafeTotalRaw,
    getStorage, getStorageAddr, getMapping, setStorage, setMapping, msgSender,
    requireSomeUint, Verity.require, Verity.bind, Bind.bind,
    Verity.pure, Pure.pure,
    ContractState.readSlot, ContractState.readAddrSlot, ContractState.readMap,
    ContractState.writeSlot, ContractState.writeMap,
    HAdd.hAdd, Add.add, beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro user
    by_cases hRecipient : user = s.storageAddr FeeHandler.managementFeeRecipient.slot
    · simp [hRecipient]
    · simp [hRecipient]
  · simpa [performanceFeeRecipientOf] using hReentryPerformanceRecipient s

theorem performance_only_exact_accounting
    (env : Verity.Env)
    (totalPositionsValue : Uint256)
    (shares : Address)
    (s : ContractState)
    (hReentry : DynamicFeeReentryStable env.reenter)
    (hValuationCall : valuationHandlerCallSucceeds env shares)
    (hCaller : s.sender = wordToAddress (valuationHandlerWord env shares))
    (hPositionsCoverPriorFees : totalFeesOwedOf s ≤ totalPositionsValue)
    (hManagementDisabled : managementFeeTrackerOf s = zeroAddress)
    (hPerformanceEnabled : performanceFeeTrackerOf s ≠ zeroAddress)
    (hPerformanceCall : performanceOnlyCallSucceeds env s totalPositionsValue)
    (hPerformanceRecipientNoOverflow :
      (feesOwedTo s (performanceFeeRecipientOf s)).val +
        (performanceOnlyFeeAmount env s totalPositionsValue).val ≤ MAX_UINT256)
    (hPerformanceTotalNoOverflow :
      (totalFeesOwedOf s).val +
        (performanceOnlyFeeAmount env s totalPositionsValue).val ≤ MAX_UINT256) :
    ∃ s',
      FeeHandler.settleDynamicFeesGivenPositionsValue env totalPositionsValue shares s =
        ContractResult.success () s' ∧
      performanceOnlyExactSettlement env s s' totalPositionsValue := by
  obtain ⟨hReentryManagementTracker, hReentryPerformanceTracker,
      hReentryManagementRecipient, hReentryPerformanceRecipient,
      hReentryTotal, hReentryUsers⟩ := dynamicFeeReentryStable_raw hReentry
  have hSafeRecipient := safeAdd_some
    (feesOwedTo s (performanceFeeRecipientOf s))
    (performanceOnlyFeeAmount env s totalPositionsValue)
    hPerformanceRecipientNoOverflow
  have hSafeTotal := safeAdd_some
    (totalFeesOwedOf s)
    (performanceOnlyFeeAmount env s totalPositionsValue)
    hPerformanceTotalNoOverflow
  have hSafeRecipientRaw :
      safeAdd
          (s.storageMap FeeHandler.userFeesOwed.slot
            (s.storageAddr FeeHandler.performanceFeeRecipient.slot))
          (performanceOnlyFeeAmount env s totalPositionsValue) =
        some
          (add
            (s.storageMap FeeHandler.userFeesOwed.slot
              (s.storageAddr FeeHandler.performanceFeeRecipient.slot))
            (performanceOnlyFeeAmount env s totalPositionsValue)) := by
    simpa [feesOwedTo, performanceFeeRecipientOf, HAdd.hAdd, Add.add] using hSafeRecipient
  have hSafeTotalRaw :
      safeAdd (s.storage FeeHandler.totalFeesOwed.slot)
          (performanceOnlyFeeAmount env s totalPositionsValue) =
        some
          (add (s.storage FeeHandler.totalFeesOwed.slot)
            (performanceOnlyFeeAmount env s totalPositionsValue)) := by
    simpa [totalFeesOwedOf, HAdd.hAdd, Add.add] using hSafeTotal
  have hValuationOracle :
      env.callOracle "externalCallSucceeded"
          (externalCallKeyWords shares getValuationHandlerSelector []) ≠ 0 := by
    intro hZero
    have h := hValuationCall
    simp [valuationHandlerCallSucceeds, externalCallSucceeded, hZero] at h
  have hPerformanceOracle :
      env.callOracle "externalCallSucceeded"
          (externalCallKeyWords (performanceFeeTrackerOf s) settlePerformanceFeeSelector
            [performanceOnlyFeeBase s totalPositionsValue]) ≠ 0 := by
    intro hZero
    have h := hPerformanceCall
    simp [performanceOnlyCallSucceeds, externalCallSucceeded, hZero] at h
  have hPositionsRaw :
      (s.storage FeeHandler.totalFeesOwed.slot).val ≤ totalPositionsValue.val := by
    simpa [totalFeesOwedOf, Verity.Core.Uint256.le_def] using hPositionsCoverPriorFees
  have hManagementDisabledRaw :
      s.storageAddr FeeHandler.managementFeeTracker.slot = (0 : Address) := by
    simpa [managementFeeTrackerOf, zeroAddress] using hManagementDisabled
  have hPerformanceEnabledRaw :
      s.storageAddr FeeHandler.performanceFeeTracker.slot ≠ (0 : Address) := by
    simpa [performanceFeeTrackerOf, zeroAddress] using hPerformanceEnabled
  have hCallerRaw :
      s.sender = wordToAddress
        (externalCallReturndata env shares getValuationHandlerSelector []) := by
    simpa [valuationHandlerWord] using hCaller
  have hSubZero :
      sub (sub totalPositionsValue (s.storage FeeHandler.totalFeesOwed.slot)) 0 =
        sub totalPositionsValue (s.storage FeeHandler.totalFeesOwed.slot) := by
    apply Verity.Core.Uint256.ext
    simp only [Verity.Core.Uint256.sub]
    simp only [Verity.Core.Uint256.val_zero, Nat.zero_le, if_pos,
      Nat.sub_zero, Verity.Core.Uint256.val_ofNat]
    exact Nat.mod_eq_of_lt
      (sub totalPositionsValue (s.storage FeeHandler.totalFeesOwed.slot)).isLt
  unfold performanceOnlyFeeAmount at hSafeRecipientRaw hSafeTotalRaw
  simp only [performanceFeeTrackerOf, performanceOnlyFeeBase, managementFeeBase, totalFeesOwedOf] at hSafeRecipientRaw hSafeTotalRaw hPerformanceOracle
  simp [performanceOnlyExactSettlement, feeHandlerStorageFrame,
    performanceOnlyCallSucceeds, performanceOnlyFeeBase, performanceOnlyFeeAmount,
    FeeHandler.settleDynamicFeesGivenPositionsValue,
    FeeHandler.__increaseValueOwed, FeeHandler.__updateValueOwed,
    runStaticWordCall, runExternalWordCall, externalCallSucceeded,
    totalFeesOwedOf, feesOwedTo,
    managementFeeTrackerOf, performanceFeeTrackerOf, performanceFeeRecipientOf,
    managementFeeBase, sub,
    hReentryManagementTracker, hReentryPerformanceTracker,
    hReentryManagementRecipient, hReentryPerformanceRecipient,
    hReentryTotal, hReentryUsers,
    hValuationOracle, hPerformanceOracle,
    hPositionsRaw, hManagementDisabledRaw, hPerformanceEnabledRaw, hCallerRaw,
    hSubZero,
    hSafeRecipientRaw, hSafeTotalRaw,
    getStorage, getStorageAddr, getMapping, setStorage, setMapping, msgSender,
    requireSomeUint, Verity.require, Verity.bind, Bind.bind,
    Verity.pure, Pure.pure,
    ContractState.readSlot, ContractState.readAddrSlot, ContractState.readMap,
    ContractState.writeSlot, ContractState.writeMap,
    HAdd.hAdd, Add.add, beq_iff_eq, decide_eq_true_eq]
  constructor
  · intro user
    by_cases hRecipient : user = s.storageAddr FeeHandler.performanceFeeRecipient.slot
    · simp [hRecipient]
    · simp [hRecipient]
  · simpa [managementFeeRecipientOf] using hReentryManagementRecipient s

/-- With both dynamic trackers disabled, successful authorization leaves state unchanged. -/
theorem both_trackers_disabled_noop
    (env : Verity.Env)
    (totalPositionsValue : Uint256)
    (shares : Address)
    (s : ContractState)
    (hValuationCall : valuationHandlerCallSucceeds env shares)
    (hCaller : s.sender = wordToAddress (valuationHandlerWord env shares))
    (hPositionsCoverPriorFees : totalFeesOwedOf s ≤ totalPositionsValue)
    (hManagementDisabled : managementFeeTrackerOf s = zeroAddress)
    (hPerformanceDisabled : performanceFeeTrackerOf s = zeroAddress) :
    FeeHandler.settleDynamicFeesGivenPositionsValue env totalPositionsValue shares s =
      ContractResult.success () s := by
  have hValuationOracle :
      env.callOracle "externalCallSucceeded"
          (externalCallKeyWords shares getValuationHandlerSelector []) ≠ 0 := by
    intro hZero
    have h := hValuationCall
    simp [valuationHandlerCallSucceeds, externalCallSucceeded, hZero] at h
  have hPositionsRaw :
      (s.storage FeeHandler.totalFeesOwed.slot).val ≤ totalPositionsValue.val := by
    simpa [totalFeesOwedOf, Verity.Core.Uint256.le_def] using hPositionsCoverPriorFees
  have hManagementDisabledRaw :
      s.storageAddr FeeHandler.managementFeeTracker.slot = (0 : Address) := by
    simpa [managementFeeTrackerOf, zeroAddress] using hManagementDisabled
  have hPerformanceDisabledRaw :
      s.storageAddr FeeHandler.performanceFeeTracker.slot = (0 : Address) := by
    simpa [performanceFeeTrackerOf, zeroAddress] using hPerformanceDisabled
  have hCallerRaw :
      s.sender = wordToAddress
        (externalCallReturndata env shares getValuationHandlerSelector []) := by
    simpa [valuationHandlerWord] using hCaller
  simp [FeeHandler.settleDynamicFeesGivenPositionsValue,
    runStaticWordCall, externalCallSucceeded,
    hValuationOracle, hCallerRaw, hPositionsRaw,
    hManagementDisabledRaw, hPerformanceDisabledRaw,
    getStorage, getStorageAddr, msgSender,
    Verity.require, Verity.bind, Bind.bind,
    Verity.pure, Pure.pure,
    ContractState.readSlot, ContractState.readAddrSlot,
    beq_iff_eq, decide_eq_true_eq]

/-- Every raw revert is normalized by `Contract.run` to the invocation state. -/
theorem settlement_revert_rolls_back
    (env : Verity.Env)
    (totalPositionsValue : Uint256)
    (shares : Address)
    (s failedState : ContractState)
    (msg : String)
    (hRawRevert :
      FeeHandler.settleDynamicFeesGivenPositionsValue env totalPositionsValue shares s =
        ContractResult.revert msg failedState) :
    ((FeeHandler.settleDynamicFeesGivenPositionsValue env totalPositionsValue shares).run s).snd = s := by
  simp [Contract.run, hRawRevert]

end Benchmark.Cases.Enzyme.OnyxFeeHandler