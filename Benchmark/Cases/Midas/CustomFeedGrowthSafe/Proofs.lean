import Benchmark.Cases.Midas.CustomFeedGrowthSafe.Specs
import Verity.Proofs.Stdlib.Automation

set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

namespace Benchmark.Cases.Midas.CustomFeedGrowthSafe

open Contracts
open Verity
open Verity.EVM.Uint256

@[simp] private theorem getStorage_apply_raw (sl : StorageSlot Uint256)
    (s : ContractState) :
    getStorage sl s = ContractResult.success (s.readSlot sl.slot) s := rfl
@[simp] private theorem setStorage_apply_raw (sl : StorageSlot Uint256)
    (value : Uint256) (s : ContractState) :
    setStorage sl value s = ContractResult.success () (s.writeSlot sl.slot value) := rfl
@[simp] private theorem getMappingUint_apply_raw (sl : StorageSlot (Uint256 → Uint256))
    (key : Uint256) (s : ContractState) :
    getMappingUint sl key s = ContractResult.success (s.readMapUint sl.slot key) s := rfl
@[simp] private theorem setMappingUint_apply_raw (sl : StorageSlot (Uint256 → Uint256))
    (key value : Uint256) (s : ContractState) :
    setMappingUint sl key value s =
      ContractResult.success () (s.writeMapUint sl.slot key value) := rfl

private theorem latestRoundSlot : CustomFeedGrowthSafe.latestRound.slot = 5 := by native_decide
private theorem onlyUpSlot : CustomFeedGrowthSafe.onlyUp.slot = 6 := by native_decide
private theorem maxAnswerDeviationSlot : CustomFeedGrowthSafe.maxAnswerDeviation.slot = 0 := by native_decide
private theorem minAnswerSlot : CustomFeedGrowthSafe.minAnswer.slot = 1 := by native_decide
private theorem maxAnswerSlot : CustomFeedGrowthSafe.maxAnswer.slot = 2 := by native_decide
private theorem minGrowthAprSlot : CustomFeedGrowthSafe.minGrowthApr.slot = 3 := by native_decide
private theorem maxGrowthAprSlot : CustomFeedGrowthSafe.maxGrowthApr.slot = 4 := by native_decide
private theorem roundAnswerSlot : CustomFeedGrowthSafe.roundAnswer.slot = 7 := by native_decide
private theorem roundStartedAtSlot : CustomFeedGrowthSafe.roundStartedAt.slot = 8 := by native_decide
private theorem roundUpdatedAtSlot : CustomFeedGrowthSafe.roundUpdatedAt.slot = 9 := by native_decide
private theorem roundGrowthAprSlot : CustomFeedGrowthSafe.roundGrowthApr.slot = 10 := by native_decide

private theorem oneNum : ONE = 100000000 := by native_decide
private theorem hundredOneNum : HUNDRED_ONE = 10000000000 := by native_decide
private theorem yearSecondsNum : YEAR_SECONDS = 31536000 := by native_decide
private theorem growthDenominatorNum : GROWTH_DENOMINATOR = 315360000000000000 := by
  native_decide
private theorem lastStartedAtRaw (s : ContractState) :
    lastStartedAtOf s = s.storageMapUint 8 (s.storage 5) := rfl
private theorem maxAnswerDeviationRaw (s : ContractState) :
    maxAnswerDeviationOf s = s.storage 0 := rfl
private theorem hourVal : (3600 : Uint256).val = 3600 := by native_decide
private theorem hundredOneVal : (10000000000 : Uint256).val = 10000000000 := by native_decide

attribute [local simp] oneNum hundredOneNum yearSecondsNum growthDenominatorNum
  lastStartedAtRaw maxAnswerDeviationRaw latestRoundSlot roundAnswerSlot
  roundStartedAtSlot roundUpdatedAtSlot roundGrowthAprSlot maxAnswerDeviationSlot
  hourVal hundredOneVal


private def setRoundWrites
    (roundId data dataTimestamp growthApr blockTimestamp : Uint256) : Contract Unit := do
  setMappingUint CustomFeedGrowthSafe.roundAnswer roundId data
  setMappingUint CustomFeedGrowthSafe.roundStartedAt roundId dataTimestamp
  setMappingUint CustomFeedGrowthSafe.roundUpdatedAt roundId blockTimestamp
  setMappingUint CustomFeedGrowthSafe.roundGrowthApr roundId growthApr
  setStorage CustomFeedGrowthSafe.latestRound roundId

private def writeStorageAfterRound (s : ContractState) (storageSlot : Nat) : Uint256 :=
  if storageSlot = CustomFeedGrowthSafe.latestRound.slot then nextRoundIdOf s else s.storage storageSlot

private def writeMapUintAfterRound
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (mappingSlot : Nat) (k : Uint256) : Uint256 :=
  let roundId := nextRoundIdOf s
  if mappingSlot = CustomFeedGrowthSafe.roundGrowthApr.slot ∧ k = roundId then growthApr
  else if mappingSlot = CustomFeedGrowthSafe.roundUpdatedAt.slot ∧ k = roundId then blockTimestamp
  else if mappingSlot = CustomFeedGrowthSafe.roundStartedAt.slot ∧ k = roundId then dataTimestamp
  else if mappingSlot = CustomFeedGrowthSafe.roundAnswer.slot ∧ k = roundId then data
  else s.storageMapUint mappingSlot k

private theorem setRoundWrites_storage
    (roundId data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState) (storageSlot : Nat) :
    (((setRoundWrites roundId data dataTimestamp growthApr blockTimestamp).run s).snd).storage storageSlot =
      if storageSlot = CustomFeedGrowthSafe.latestRound.slot then roundId else s.storage storageSlot := by
  simp [setRoundWrites, setStorage, setMappingUint, Verity.bind, Bind.bind, Contract.run, ContractResult.snd]

private theorem setRoundWrites_storageMapUint
    (roundId data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (mappingSlot : Nat) (k : Uint256) :
    (((setRoundWrites roundId data dataTimestamp growthApr blockTimestamp).run s).snd).storageMapUint mappingSlot k =
      if mappingSlot = CustomFeedGrowthSafe.roundGrowthApr.slot ∧ k = roundId then growthApr
      else if mappingSlot = CustomFeedGrowthSafe.roundUpdatedAt.slot ∧ k = roundId then blockTimestamp
      else if mappingSlot = CustomFeedGrowthSafe.roundStartedAt.slot ∧ k = roundId then dataTimestamp
      else if mappingSlot = CustomFeedGrowthSafe.roundAnswer.slot ∧ k = roundId then data
      else s.storageMapUint mappingSlot k := by
  simp [setRoundWrites, setStorage, setMappingUint, Verity.bind, Bind.bind, Contract.run, ContractResult.snd]

private theorem setRoundData_writes
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hDataLoBranch : ¬ (slt data (s.storage CustomFeedGrowthSafe.minAnswer.slot) = true))
    (hDataHiBranch : ¬ (sgt data (s.storage CustomFeedGrowthSafe.maxAnswer.slot) = true))
    (hGrowthLoBranch :
      ¬ (slt growthApr (s.storage CustomFeedGrowthSafe.minGrowthApr.slot) = true))
    (hGrowthHiBranch :
      ¬ (sgt growthApr (s.storage CustomFeedGrowthSafe.maxGrowthApr.slot) = true))
    (hDataTsLt : dataTimestamp < blockTimestamp)
    (storageSlot mapSlot : Nat) (k : Uint256) :
    let s' := ((CustomFeedGrowthSafe.setRoundData data dataTimestamp growthApr blockTimestamp).run s).snd
    s'.storage storageSlot = writeStorageAfterRound s storageSlot ∧
      s'.storageMapUint mapSlot k = writeMapUintAfterRound data dataTimestamp growthApr blockTimestamp s mapSlot k := by
  unfold CustomFeedGrowthSafe.setRoundData Verity.require
  simp only [getStorage, getMappingUint, setStorage, setMappingUint, Verity.bind, Bind.bind, Pure.pure,
    Contract.run, ContractResult.snd]
  constructor
  · simp [hDataLoBranch, hDataHiBranch, hGrowthLoBranch, hGrowthHiBranch, hDataTsLt,
      Verity.bind, Bind.bind, Contract.run, getStorage, getMappingUint, setStorage,
      setMappingUint, writeStorageAfterRound, nextRoundIdOf, latestRoundOf,
      latestRoundSlot, ContractState.writeSlot, ContractState.writeMapUint]
  · simp [hDataLoBranch, hDataHiBranch, hGrowthLoBranch, hGrowthHiBranch, hDataTsLt,
      Verity.bind, Bind.bind, Contract.run, getStorage, getMappingUint, setStorage,
      setMappingUint, writeMapUintAfterRound, nextRoundIdOf, latestRoundOf,
      latestRoundSlot, roundGrowthAprSlot, roundUpdatedAtSlot, roundStartedAtSlot,
      roundAnswerSlot, ContractState.writeSlot, ContractState.writeMapUint]

private theorem applyGrowth_eval
    (answer growthApr timestampFrom blockTimestamp : Uint256) (s : ContractState)
    (hTime : timestampFrom ≤ blockTimestamp) :
    ((CustomFeedGrowthSafe.applyGrowth answer growthApr timestampFrom blockTimestamp).run s) =
      ContractResult.success (applyGrowthAtRaw answer growthApr timestampFrom blockTimestamp) s := by
  unfold CustomFeedGrowthSafe.applyGrowth CustomFeedGrowthSafe.applyGrowthAt Verity.require applyGrowthAtRaw
  simpa [Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, hTime,
    GROWTH_DENOMINATOR]

private theorem lastAnswer_eval
    (blockTimestamp : Uint256) (s : ContractState)
    (hTime : lastStartedAtOf s ≤ blockTimestamp) :
    ((CustomFeedGrowthSafe.lastAnswer blockTimestamp).run s) =
      ContractResult.success (lastAnswerOf s blockTimestamp) s := by
  unfold CustomFeedGrowthSafe.lastAnswer
  simp [CustomFeedGrowthSafe.lastRawAnswer, CustomFeedGrowthSafe.lastGrowthApr, CustomFeedGrowthSafe.lastStartedAt,
    getStorage, getMappingUint, Verity.bind, Bind.bind, Contract.run]
  simpa [lastAnswerOf, lastRawAnswerOf, lastGrowthAprOf, lastStartedAtOf, latestRoundOf, roundAnswerOf,
    roundGrowthAprOf, roundStartedAtOf, applyGrowthNowRaw, applyGrowthAtRaw,
    latestRoundSlot, roundAnswerSlot, roundGrowthAprSlot, roundStartedAtSlot,
    getStorage, getMappingUint, Verity.bind, Bind.bind, Contract.run,
    Verity.require, Verity.pure, Pure.pure] using
    (applyGrowth_eval (s.storageMapUint 7 (s.storage 5)) (s.storageMapUint 10 (s.storage 5))
      (s.storageMapUint 8 (s.storage 5)) blockTimestamp s (by
        simpa [lastStartedAtOf, roundStartedAtOf, latestRoundOf] using hTime))

private theorem lastTimestamp_eval
    (s : ContractState) :
    (CustomFeedGrowthSafe.lastTimestamp.run s) =
      ContractResult.success (lastTimestampOf s) s := by
  unfold CustomFeedGrowthSafe.lastTimestamp
  simp [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, getStorage, getMappingUint,
    Verity.bind, Bind.bind, Contract.run, latestRoundSlot, roundUpdatedAtSlot]

private theorem lastStartedAt_eval
    (s : ContractState) :
    (CustomFeedGrowthSafe.lastStartedAt.run s) =
      ContractResult.success (lastStartedAtOf s) s := by
  unfold CustomFeedGrowthSafe.lastStartedAt
  simp [lastStartedAtOf, roundStartedAtOf, latestRoundOf, getStorage, getMappingUint,
    Verity.bind, Bind.bind, Contract.run, latestRoundSlot, roundStartedAtSlot]

private theorem lastGrowthApr_eval
    (s : ContractState) :
    (CustomFeedGrowthSafe.lastGrowthApr.run s) =
      ContractResult.success (lastGrowthAprOf s) s := by
  unfold CustomFeedGrowthSafe.lastGrowthApr
  simp [lastGrowthAprOf, roundGrowthAprOf, latestRoundOf, getStorage, getMappingUint,
    Verity.bind, Bind.bind, Contract.run, latestRoundSlot, roundGrowthAprSlot]

private theorem lastRawAnswer_eval
    (s : ContractState) :
    (CustomFeedGrowthSafe.lastRawAnswer.run s) =
      ContractResult.success (lastRawAnswerOf s) s := by
  unfold CustomFeedGrowthSafe.lastRawAnswer
  simp [lastRawAnswerOf, roundAnswerOf, latestRoundOf, getStorage, getMappingUint,
    Verity.bind, Bind.bind, Contract.run, latestRoundSlot, roundAnswerSlot]

private theorem getDeviation_eval_false_neg
    (lastPrice newPrice : Uint256) (s : ContractState)
    (hNewNZ : newPrice ≠ 0)
    (hLastNZ : lastPrice ≠ 0)
    (hNeg : slt (signedDeviationRaw lastPrice newPrice) 0 = true) :
    ((CustomFeedGrowthSafe._getDeviation lastPrice newPrice false).run s) =
      ContractResult.success (sub 0 (signedDeviationRaw lastPrice newPrice)) s := by
  have hNeg' : slt (sdiv (mul (mul (sub newPrice lastPrice) ONE) 100) lastPrice) 0 = true := by
    simpa [signedDeviationRaw] using hNeg
  unfold CustomFeedGrowthSafe._getDeviation Verity.require signedDeviationRaw
  simpa [Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, hNewNZ, hLastNZ, hNeg']

private theorem getDeviation_eval_false_nonneg
    (lastPrice newPrice : Uint256) (s : ContractState)
    (hNewNZ : newPrice ≠ 0)
    (hLastNZ : lastPrice ≠ 0)
    (hNeg : slt (signedDeviationRaw lastPrice newPrice) 0 = false) :
    ((CustomFeedGrowthSafe._getDeviation lastPrice newPrice false).run s) =
      ContractResult.success (signedDeviationRaw lastPrice newPrice) s := by
  have hNeg' : slt (sdiv (mul (mul (sub newPrice lastPrice) ONE) 100) lastPrice) 0 = false := by
    simpa [signedDeviationRaw] using hNeg
  unfold CustomFeedGrowthSafe._getDeviation Verity.require signedDeviationRaw
  simpa [Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, hNewNZ, hLastNZ, hNeg']

private theorem getDeviation_eval_true_nonneg
    (lastPrice newPrice : Uint256) (s : ContractState)
    (hNewNZ : newPrice ≠ 0)
    (hLastNZ : lastPrice ≠ 0)
    (hNeg : slt (signedDeviationRaw lastPrice newPrice) 0 = false) :
    ((CustomFeedGrowthSafe._getDeviation lastPrice newPrice true).run s) =
      ContractResult.success (signedDeviationRaw lastPrice newPrice) s := by
  have hNeg' : slt (sdiv (mul (mul (sub newPrice lastPrice) ONE) 100) lastPrice) 0 = false := by
    simpa [signedDeviationRaw] using hNeg
  unfold CustomFeedGrowthSafe._getDeviation Verity.require signedDeviationRaw
  simpa [Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, hNewNZ, hLastNZ, hNeg']

private theorem getDeviation_revert_last_zero
    (newPrice : Uint256) (validateOnlyUp : Bool) (s : ContractState)
    (hNewNZ : newPrice ≠ 0) :
    ((CustomFeedGrowthSafe._getDeviation 0 newPrice validateOnlyUp).run s) =
      ContractResult.revert "CAG: last price is zero" s := by
  unfold CustomFeedGrowthSafe._getDeviation Verity.require
  simp [Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, hNewNZ]

private theorem getDeviation_eval_zero_price
    (lastPrice : Uint256) (validateOnlyUp : Bool) (s : ContractState) :
    ((CustomFeedGrowthSafe._getDeviation lastPrice 0 validateOnlyUp).run s) =
      ContractResult.success HUNDRED_ONE s := by
  unfold CustomFeedGrowthSafe._getDeviation Verity.require
  simp [Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, HUNDRED_ONE]

private theorem getDeviation_revert_true_neg
    (lastPrice newPrice : Uint256) (s : ContractState)
    (hNewNZ : newPrice ≠ 0)
    (hLastNZ : lastPrice ≠ 0)
    (hNeg : slt (signedDeviationRaw lastPrice newPrice) 0 = true) :
    ((CustomFeedGrowthSafe._getDeviation lastPrice newPrice true).run s) =
      ContractResult.revert "CAG: deviation is negative" s := by
  have hNeg' : slt (sdiv (mul (mul (sub newPrice lastPrice) ONE) 100) lastPrice) 0 = true := by
    simpa [signedDeviationRaw] using hNeg
  unfold CustomFeedGrowthSafe._getDeviation Verity.require
  simp [Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, hNewNZ, hLastNZ, hNeg']

private theorem getDeviation_success_implies_specs
    (lastPrice newPrice : Uint256) (validateOnlyUp : Bool) (s s' : ContractState)
    (deviation : Uint256)
    (hRun :
      ((CustomFeedGrowthSafe._getDeviation lastPrice newPrice validateOnlyUp).run s) =
        ContractResult.success deviation s') :
    s' = s ∧
      deviation = deviationAbsRaw lastPrice newPrice ∧
      (newPrice ≠ 0 → (lastPrice != 0) = true) ∧
      (newPrice ≠ 0 → validateOnlyUp = true →
        slt (signedDeviationRaw lastPrice newPrice) 0 = false) := by
  by_cases hNewZero : newPrice = 0
  · unfold CustomFeedGrowthSafe._getDeviation at hRun
    simp [hNewZero, Verity.pure, Pure.pure, Contract.run, HUNDRED_ONE] at hRun
    rcases hRun with ⟨hDev, hState⟩
    subst deviation
    subst s'
    simp [deviationAbsRaw, hNewZero, HUNDRED_ONE]
  · by_cases hLastZero : lastPrice = 0
    · unfold CustomFeedGrowthSafe._getDeviation Verity.require at hRun
      simp [hNewZero, hLastZero, Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run] at hRun
    · have hLastNZBool : (lastPrice != 0) = true := by
        simpa [hLastZero]
      cases hValidate : validateOnlyUp
      · by_cases hNeg : slt (signedDeviationRaw lastPrice newPrice) 0 = true
        · unfold CustomFeedGrowthSafe._getDeviation Verity.require at hRun
          have hNegRaw :
              slt (sdiv (mul (mul (sub newPrice lastPrice) ONE) 100) lastPrice) 0 = true := by
            simpa [signedDeviationRaw] using hNeg
          simp [hNewZero, hLastZero, hLastNZBool, hValidate, hNegRaw,
            Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run] at hRun
          rcases hRun with ⟨hDev, hState⟩
          subst deviation
          subst s'
          simp [deviationAbsRaw, absSignedWord, signedDeviationRaw, hNewZero, hNeg, hNegRaw,
            hLastNZBool]
        · have hNegFalse : slt (signedDeviationRaw lastPrice newPrice) 0 = false := by
            cases hBool : slt (signedDeviationRaw lastPrice newPrice) 0 <;> simp [hBool] at hNeg ⊢
          unfold CustomFeedGrowthSafe._getDeviation Verity.require at hRun
          have hNegRawFalse :
              slt (sdiv (mul (mul (sub newPrice lastPrice) ONE) 100) lastPrice) 0 = false := by
            simpa [signedDeviationRaw] using hNegFalse
          simp [hNewZero, hLastZero, hLastNZBool, hValidate, hNegRawFalse,
            Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run] at hRun
          rcases hRun with ⟨hDev, hState⟩
          subst deviation
          subst s'
          simp [deviationAbsRaw, absSignedWord, signedDeviationRaw, hNewZero, hNegFalse,
            hNegRawFalse, hLastNZBool]
      · by_cases hNeg : slt (signedDeviationRaw lastPrice newPrice) 0 = true
        · unfold CustomFeedGrowthSafe._getDeviation Verity.require at hRun
          have hNegRaw :
              slt (sdiv (mul (mul (sub newPrice lastPrice) ONE) 100) lastPrice) 0 = true := by
            simpa [signedDeviationRaw] using hNeg
          simp [hNewZero, hLastZero, hLastNZBool, hValidate, hNegRaw,
            Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run] at hRun
        · have hNegFalse : slt (signedDeviationRaw lastPrice newPrice) 0 = false := by
            cases hBool : slt (signedDeviationRaw lastPrice newPrice) 0 <;> simp [hBool] at hNeg ⊢
          unfold CustomFeedGrowthSafe._getDeviation Verity.require at hRun
          have hNegRawFalse :
              slt (sdiv (mul (mul (sub newPrice lastPrice) ONE) 100) lastPrice) 0 = false := by
            simpa [signedDeviationRaw] using hNegFalse
          simp [hNewZero, hLastZero, hLastNZBool, hValidate, hNegRawFalse,
            Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run] at hRun
          rcases hRun with ⟨hDev, hState⟩
          subst deviation
          subst s'
          simp [deviationAbsRaw, absSignedWord, signedDeviationRaw, hNewZero, hNegFalse,
            hNegRawFalse, hLastNZBool]

private theorem bind_run_success_same_state
    {α β : Type} (c : Contract α) (f : α → Contract β) (s : ContractState) (a : α)
    (h : c.run s = ContractResult.success a s) :
    (Verity.bind c f).run s = (f a).run s := by
  have hc : c s = ContractResult.success a s := Contract.eq_of_run_success h
  unfold Contract.run Verity.bind
  simp [hc]

private theorem bind_isSuccess_right_same_state
    {α β : Type} (c : Contract α) (f : α → Contract β) (s : ContractState) (a : α)
    (hRun : c.run s = ContractResult.success a s)
    (hSuccess : ((Verity.bind c f).run s).isSuccess = true) :
    ((f a).run s).isSuccess = true := by
  rw [bind_run_success_same_state c f s a hRun] at hSuccess
  exact hSuccess

private theorem bind_run_revert_same_state
    {α β : Type} (c : Contract α) (f : α → Contract β) (s : ContractState) (msg : String)
    (h : c.run s = ContractResult.revert msg s) :
    (Verity.bind c f).run s = ContractResult.revert msg s := by
  unfold Contract.run at h ⊢
  cases hC : c s
  · simp [Verity.bind, hC] at h
  · simp [Verity.bind, hC] at h ⊢
    cases h
    rfl

private def setRoundDataSafeTimeTail
    {α : Type} (_lastUpdatedAt dataTimestamp blockTimestamp : Uint256) (k : Unit → Contract α) :
    Contract α := do
  require (_lastUpdatedAt <= blockTimestamp) "CAG: timestamp underflow"
  require (sub blockTimestamp _lastUpdatedAt > 3600) "CAG: not enough time passed"
  let __do_lift ← CustomFeedGrowthSafe.lastStartedAt
  require (dataTimestamp > __do_lift) "CAG: timestamp <= last startedAt"
  k ()

private def setRoundDataSafeOnlyUpTail
    {α : Type} (_onlyUp _lastUpdatedAt dataTimestamp growthApr blockTimestamp : Uint256)
    (k : Unit → Contract α) : Contract α := do
  if _onlyUp != 0 then
    if slt growthApr 0 then
      let _y ← require false "CAG: negative apr"
      setRoundDataSafeTimeTail _lastUpdatedAt dataTimestamp blockTimestamp k
    else
      let _y ← (Pure.pure () : Contract Unit)
      setRoundDataSafeTimeTail _lastUpdatedAt dataTimestamp blockTimestamp k
  else
    let _y ← (Pure.pure () : Contract Unit)
    setRoundDataSafeTimeTail _lastUpdatedAt dataTimestamp blockTimestamp k

private def setRoundDataSafeHistoryTail
    {α : Type} (_onlyUp _lastUpdatedAt data dataTimestamp growthApr blockTimestamp : Uint256)
    (k : Unit → Contract α) : Contract α := do
  if _lastUpdatedAt != 0 then
    let __do_lift ← CustomFeedGrowthSafe.lastAnswer blockTimestamp
    let __do_lift_1 ← CustomFeedGrowthSafe.applyGrowth data growthApr dataTimestamp blockTimestamp
    let deviation ← CustomFeedGrowthSafe._getDeviation __do_lift __do_lift_1 (_onlyUp != 0)
    let maxAnswerDeviation_ ← getStorage CustomFeedGrowthSafe.maxAnswerDeviation
    let _y ← require (deviation <= maxAnswerDeviation_) "CAG: !deviation"
    setRoundDataSafeOnlyUpTail _onlyUp _lastUpdatedAt dataTimestamp growthApr blockTimestamp k
  else
    let _y ← (Pure.pure () : Contract Unit)
    setRoundDataSafeOnlyUpTail _onlyUp _lastUpdatedAt dataTimestamp growthApr blockTimestamp k

private def setRoundDataSafeWithTail
    {α : Type} (data dataTimestamp growthApr blockTimestamp : Uint256) (k : Unit → Contract α) :
    Contract α := do
  let _onlyUp ← getStorage CustomFeedGrowthSafe.onlyUp
  let _lastUpdatedAt ← CustomFeedGrowthSafe.lastTimestamp
  setRoundDataSafeHistoryTail _onlyUp _lastUpdatedAt data dataTimestamp growthApr blockTimestamp k

private theorem setRoundDataSafe_eq_with_tail
    (data dataTimestamp growthApr blockTimestamp : Uint256) :
    CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp =
      setRoundDataSafeWithTail data dataTimestamp growthApr blockTimestamp
        (fun _ => CustomFeedGrowthSafe.setRoundData data dataTimestamp growthApr blockTimestamp) := by
  rfl

private theorem applyGrowth_revert
    (answer growthApr timestampFrom blockTimestamp : Uint256) (s : ContractState)
    (hTime : ¬ timestampFrom ≤ blockTimestamp) :
    ((CustomFeedGrowthSafe.applyGrowth answer growthApr timestampFrom blockTimestamp).run s) =
      ContractResult.revert "CAG: timestampTo < timestampFrom" s := by
  unfold CustomFeedGrowthSafe.applyGrowth CustomFeedGrowthSafe.applyGrowthAt Verity.require
  simp [Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run, hTime]

private theorem lastAnswer_revert
    (blockTimestamp : Uint256) (s : ContractState)
    (hTime : ¬ lastStartedAtOf s ≤ blockTimestamp) :
    ((CustomFeedGrowthSafe.lastAnswer blockTimestamp).run s) =
      ContractResult.revert "CAG: timestampTo < timestampFrom" s := by
  have hLastRawAnswerEval :
      (CustomFeedGrowthSafe.lastRawAnswer.run s) =
        ContractResult.success (lastRawAnswerOf s) s := by
    exact lastRawAnswer_eval s
  have hLastGrowthAprEval :
      (CustomFeedGrowthSafe.lastGrowthApr.run s) =
        ContractResult.success (lastGrowthAprOf s) s := by
    exact lastGrowthApr_eval s
  have hLastStartedAtEval :
      (CustomFeedGrowthSafe.lastStartedAt.run s) =
        ContractResult.success (lastStartedAtOf s) s := by
    exact lastStartedAt_eval s
  have hApplyGrowthRevert :
      ((CustomFeedGrowthSafe.applyGrowth (lastRawAnswerOf s) (lastGrowthAprOf s)
          (lastStartedAtOf s) blockTimestamp).run s) =
        ContractResult.revert "CAG: timestampTo < timestampFrom" s := by
    exact applyGrowth_revert (lastRawAnswerOf s) (lastGrowthAprOf s) (lastStartedAtOf s)
      blockTimestamp s hTime
  unfold CustomFeedGrowthSafe.lastAnswer
  simp only [Bind.bind]
  rw [bind_run_success_same_state _ _ _ _ hLastRawAnswerEval]
  rw [bind_run_success_same_state _ _ _ _ hLastGrowthAprEval]
  rw [bind_run_success_same_state _ _ _ _ hLastStartedAtEval]
  exact hApplyGrowthRevert

private theorem applyGrowth_success_implies_time
    (answer growthApr timestampFrom blockTimestamp : Uint256) (s : ContractState)
    (hSuccess :
      ((CustomFeedGrowthSafe.applyGrowth answer growthApr timestampFrom blockTimestamp).run s).isSuccess =
        true) :
    timestampFrom ≤ blockTimestamp := by
  by_cases hTime : timestampFrom ≤ blockTimestamp
  · exact hTime
  · have hRevert := applyGrowth_revert answer growthApr timestampFrom blockTimestamp s hTime
    rw [hRevert] at hSuccess
    simp [ContractResult.isSuccess] at hSuccess

private theorem lastAnswer_success_implies_time
    (blockTimestamp : Uint256) (s : ContractState)
    (hSuccess : ((CustomFeedGrowthSafe.lastAnswer blockTimestamp).run s).isSuccess = true) :
    lastStartedAtOf s ≤ blockTimestamp := by
  by_cases hTime : lastStartedAtOf s ≤ blockTimestamp
  · exact hTime
  · have hRevert := lastAnswer_revert blockTimestamp s hTime
    rw [hRevert] at hSuccess
    simp [ContractResult.isSuccess] at hSuccess

private theorem setRoundDataSafeTimeTail_success_implies
    {α : Type} (_lastUpdatedAt dataTimestamp blockTimestamp : Uint256) (s : ContractState)
    (k : Unit → Contract α)
    (hSuccess : ((setRoundDataSafeTimeTail _lastUpdatedAt dataTimestamp blockTimestamp k).run s).isSuccess =
      true) :
    _lastUpdatedAt <= blockTimestamp ∧
      sub blockTimestamp _lastUpdatedAt > 3600 ∧
      dataTimestamp > lastStartedAtOf s ∧
      ((k ()).run s).isSuccess = true := by
  have hBase := hSuccess
  unfold setRoundDataSafeTimeTail at hBase
  simp only [Bind.bind] at hBase
  have hFirstSuccess :
      ((require (decide (_lastUpdatedAt <= blockTimestamp)) "CAG: timestamp underflow").run s).isSuccess =
        true :=
    Verity.Proofs.Stdlib.Automation.bind_isSuccess_left _ _ _ hBase
  have hFirstCond :
      decide (_lastUpdatedAt <= blockTimestamp) = true :=
    Verity.Proofs.Stdlib.Automation.require_success_implies_cond
      (decide (_lastUpdatedAt <= blockTimestamp)) "CAG: timestamp underflow" s hFirstSuccess
  have hTimeOrder : _lastUpdatedAt <= blockTimestamp := by
    simpa using hFirstCond
  have hFirstRun :
      (require (decide (_lastUpdatedAt <= blockTimestamp)) "CAG: timestamp underflow").run s =
        ContractResult.success () s := by
    simp [Verity.require, hTimeOrder, Contract.run]
  have hAfterFirst :
      ((Verity.bind
            (require (decide (sub blockTimestamp _lastUpdatedAt > 3600))
              "CAG: not enough time passed")
            (fun _ =>
              Verity.bind CustomFeedGrowthSafe.lastStartedAt fun __do_lift =>
                Verity.bind
                  (require (decide (dataTimestamp > __do_lift)) "CAG: timestamp <= last startedAt")
                  (fun _ => k ()))).run s).isSuccess =
        true :=
    bind_isSuccess_right_same_state
      (require (decide (_lastUpdatedAt <= blockTimestamp)) "CAG: timestamp underflow")
      (fun _ =>
        Verity.bind
          (require (decide (sub blockTimestamp _lastUpdatedAt > 3600))
            "CAG: not enough time passed")
          (fun _ =>
            Verity.bind CustomFeedGrowthSafe.lastStartedAt fun __do_lift =>
              Verity.bind
                (require (decide (dataTimestamp > __do_lift)) "CAG: timestamp <= last startedAt")
                (fun _ => k ())))
      s () hFirstRun hBase
  have hSecondSuccess :
      ((require (decide (sub blockTimestamp _lastUpdatedAt > 3600))
          "CAG: not enough time passed").run s).isSuccess =
        true :=
    Verity.Proofs.Stdlib.Automation.bind_isSuccess_left _ _ _ hAfterFirst
  have hSecondCond :
      decide (sub blockTimestamp _lastUpdatedAt > 3600) = true :=
    Verity.Proofs.Stdlib.Automation.require_success_implies_cond
      (decide (sub blockTimestamp _lastUpdatedAt > 3600)) "CAG: not enough time passed" s hSecondSuccess
  have hGap : sub blockTimestamp _lastUpdatedAt > 3600 := by
    simpa using hSecondCond
  have hSecondRun :
      (require (decide (sub blockTimestamp _lastUpdatedAt > 3600))
          "CAG: not enough time passed").run s =
        ContractResult.success () s := by
    simp [Verity.require, hGap, Contract.run]
  have hAfterSecond :
      ((Verity.bind CustomFeedGrowthSafe.lastStartedAt fun __do_lift =>
          Verity.bind
            (require (decide (dataTimestamp > __do_lift)) "CAG: timestamp <= last startedAt")
            (fun _ => k ())).run s).isSuccess =
        true :=
    bind_isSuccess_right_same_state
      (require (decide (sub blockTimestamp _lastUpdatedAt > 3600))
        "CAG: not enough time passed")
      (fun _ =>
        Verity.bind CustomFeedGrowthSafe.lastStartedAt fun __do_lift =>
          Verity.bind
            (require (decide (dataTimestamp > __do_lift)) "CAG: timestamp <= last startedAt")
            (fun _ => k ()))
      s () hSecondRun hAfterFirst
  have hLastStartedEval :
      (CustomFeedGrowthSafe.lastStartedAt.run s) =
        ContractResult.success (lastStartedAtOf s) s := by
    exact lastStartedAt_eval s
  have hAfterLastStarted :
      ((Verity.bind
          (require (decide (dataTimestamp > lastStartedAtOf s)) "CAG: timestamp <= last startedAt")
          (fun _ => k ())).run s).isSuccess =
        true :=
    bind_isSuccess_right_same_state
      CustomFeedGrowthSafe.lastStartedAt
      (fun __do_lift =>
        Verity.bind
          (require (decide (dataTimestamp > __do_lift)) "CAG: timestamp <= last startedAt")
          (fun _ => k ()))
      s (lastStartedAtOf s) hLastStartedEval hAfterSecond
  have hThirdSuccess :
      ((require (decide (dataTimestamp > lastStartedAtOf s))
          "CAG: timestamp <= last startedAt").run s).isSuccess =
        true :=
    Verity.Proofs.Stdlib.Automation.bind_isSuccess_left _ _ _ hAfterLastStarted
  have hThirdCond :
      decide (dataTimestamp > lastStartedAtOf s) = true :=
    Verity.Proofs.Stdlib.Automation.require_success_implies_cond
      (decide (dataTimestamp > lastStartedAtOf s)) "CAG: timestamp <= last startedAt" s hThirdSuccess
  have hStarted : dataTimestamp > lastStartedAtOf s := by
    simpa using hThirdCond
  have hThirdRun :
      (require (decide (dataTimestamp > lastStartedAtOf s)) "CAG: timestamp <= last startedAt").run s =
        ContractResult.success () s := by
    simp [Verity.require, hStarted, Contract.run]
  have hAfterThird :
      ((k ()).run s).isSuccess = true :=
    bind_isSuccess_right_same_state
      (require (decide (dataTimestamp > lastStartedAtOf s)) "CAG: timestamp <= last startedAt")
      (fun _ => k ())
      s () hThirdRun hAfterLastStarted
  exact ⟨hTimeOrder, hGap, hStarted, hAfterThird⟩

private theorem setRoundDataSafeOnlyUpTail_success_implies
    {α : Type} (_onlyUp _lastUpdatedAt dataTimestamp growthApr blockTimestamp : Uint256)
    (s : ContractState) (k : Unit → Contract α)
    (hSuccess :
      ((setRoundDataSafeOnlyUpTail _onlyUp _lastUpdatedAt dataTimestamp growthApr blockTimestamp k).run s).isSuccess =
        true) :
    ((_onlyUp != 0) = true → slt growthApr 0 = false) ∧
      _lastUpdatedAt <= blockTimestamp ∧
      sub blockTimestamp _lastUpdatedAt > 3600 ∧
      dataTimestamp > lastStartedAtOf s ∧
      ((k ()).run s).isSuccess = true := by
  have hTimeTailSuccess :
      ((setRoundDataSafeTimeTail _lastUpdatedAt dataTimestamp blockTimestamp k).run s).isSuccess =
        true := by
    unfold setRoundDataSafeOnlyUpTail at hSuccess
    by_cases hOnlyUp : (_onlyUp != 0) = true
    · by_cases hNeg : slt growthApr 0 = true
      · simp [hOnlyUp, hNeg, Verity.require, Verity.bind, Bind.bind, Contract.run,
          ContractResult.isSuccess] at hSuccess
      · simpa [hOnlyUp, hNeg, Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run] using
          hSuccess
    · simpa [hOnlyUp, Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run] using hSuccess
  have hTime := setRoundDataSafeTimeTail_success_implies _lastUpdatedAt dataTimestamp blockTimestamp s k
    hTimeTailSuccess
  have hOnlyUpApr : (_onlyUp != 0) = true → slt growthApr 0 = false := by
    intro hOnlyUp
    by_cases hNeg : slt growthApr 0 = true
    · have hBad := hSuccess
      unfold setRoundDataSafeOnlyUpTail at hBad
      simp [hOnlyUp, hNeg, Verity.require, Verity.bind, Bind.bind, Contract.run,
        ContractResult.isSuccess] at hBad
    · cases hBool : slt growthApr 0 <;> simp [hBool] at hNeg ⊢
  exact ⟨hOnlyUpApr, hTime.1, hTime.2.1, hTime.2.2.1, hTime.2.2.2⟩

private theorem setRoundDataSafeHistoryTail_success_implies
    {α : Type} (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (k : Unit → Contract α)
    (hSuccess :
      ((setRoundDataSafeHistoryTail (onlyUpWordOf s) (lastTimestampOf s)
          data dataTimestamp growthApr blockTimestamp k).run s).isSuccess =
        true) :
    historyChecksPass data dataTimestamp growthApr blockTimestamp s ∧
      ((onlyUpWordOf s != 0) = true → slt growthApr 0 = false) ∧
      lastTimestampOf s <= blockTimestamp ∧
      sub blockTimestamp (lastTimestampOf s) > 3600 ∧
      dataTimestamp > lastStartedAtOf s ∧
      ((k ()).run s).isSuccess = true := by
  by_cases hNoHistory : lastTimestampOf s = 0
  · have hNoHistoryBranch :
        ¬ ((lastTimestampOf s != 0) = true) := by
      simpa [hNoHistory]
    have hTailSuccess :
        ((setRoundDataSafeOnlyUpTail (onlyUpWordOf s) (lastTimestampOf s) dataTimestamp growthApr
            blockTimestamp k).run s).isSuccess =
          true := by
      unfold setRoundDataSafeHistoryTail at hSuccess
      simpa [hNoHistoryBranch, Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run] using
        hSuccess
    have hTail :=
      setRoundDataSafeOnlyUpTail_success_implies (onlyUpWordOf s) (lastTimestampOf s)
        dataTimestamp growthApr blockTimestamp s k hTailSuccess
    have hHistoryChecks : historyChecksPass data dataTimestamp growthApr blockTimestamp s := by
      unfold historyChecksPass hasHistory
      intro hHistory
      simpa [hNoHistory] using hHistory
    exact ⟨hHistoryChecks, hTail.1, hTail.2.1, hTail.2.2.1, hTail.2.2.2.1, hTail.2.2.2.2⟩
  · have hHasHistory : ((lastTimestampOf s != 0) = true) := by
      simpa using hNoHistory
    have hBase := hSuccess
    unfold setRoundDataSafeHistoryTail at hBase
    rw [if_pos hHasHistory] at hBase
    have hLastAnswerSuccess :
        ((CustomFeedGrowthSafe.lastAnswer blockTimestamp).run s).isSuccess = true :=
      Verity.Proofs.Stdlib.Automation.bind_isSuccess_left _ _ _ hBase
    have hPrevStarted := lastAnswer_success_implies_time blockTimestamp s hLastAnswerSuccess
    have hLastAnswerEval := lastAnswer_eval blockTimestamp s hPrevStarted
    have hAfterLastAnswer :
        ((Verity.bind (CustomFeedGrowthSafe.applyGrowth data growthApr dataTimestamp blockTimestamp)
            (fun __do_lift_1 =>
              Verity.bind
                (CustomFeedGrowthSafe._getDeviation (lastAnswerOf s blockTimestamp) __do_lift_1
                  (onlyUpWordOf s != 0))
                (fun deviation =>
                  Verity.bind (getStorage CustomFeedGrowthSafe.maxAnswerDeviation)
                    (fun maxAnswerDeviation_ =>
                      Verity.bind (require (decide (deviation <= maxAnswerDeviation_)) "CAG: !deviation")
                        (fun _ =>
                          setRoundDataSafeOnlyUpTail (onlyUpWordOf s) (lastTimestampOf s)
                            dataTimestamp growthApr blockTimestamp k))))).run s).isSuccess =
          true :=
      bind_isSuccess_right_same_state
        (CustomFeedGrowthSafe.lastAnswer blockTimestamp)
        (fun __do_lift =>
          Verity.bind (CustomFeedGrowthSafe.applyGrowth data growthApr dataTimestamp blockTimestamp)
            (fun __do_lift_1 =>
              Verity.bind
                (CustomFeedGrowthSafe._getDeviation __do_lift __do_lift_1 (onlyUpWordOf s != 0))
                (fun deviation =>
                  Verity.bind (getStorage CustomFeedGrowthSafe.maxAnswerDeviation)
                    (fun maxAnswerDeviation_ =>
                      Verity.bind (require (decide (deviation <= maxAnswerDeviation_)) "CAG: !deviation")
                        (fun _ =>
                          setRoundDataSafeOnlyUpTail (onlyUpWordOf s) (lastTimestampOf s)
                            dataTimestamp growthApr blockTimestamp k)))))
        s (lastAnswerOf s blockTimestamp) hLastAnswerEval hBase
    have hCandidateSuccess :
        ((CustomFeedGrowthSafe.applyGrowth data growthApr dataTimestamp blockTimestamp).run s).isSuccess =
          true :=
      Verity.Proofs.Stdlib.Automation.bind_isSuccess_left _ _ _ hAfterLastAnswer
    have hDataTsLe := applyGrowth_success_implies_time data growthApr dataTimestamp blockTimestamp s
      hCandidateSuccess
    have hCandidateEval :
        ((CustomFeedGrowthSafe.applyGrowth data growthApr dataTimestamp blockTimestamp).run s) =
          ContractResult.success (candidateLivePrice data dataTimestamp growthApr blockTimestamp) s := by
      simpa [candidateLivePrice, applyGrowthNowRaw] using
        (applyGrowth_eval data growthApr dataTimestamp blockTimestamp s hDataTsLe)
    have hAfterCandidate :
        ((Verity.bind
            (CustomFeedGrowthSafe._getDeviation (lastAnswerOf s blockTimestamp)
              (candidateLivePrice data dataTimestamp growthApr blockTimestamp) (onlyUpWordOf s != 0))
            (fun deviation =>
              Verity.bind (getStorage CustomFeedGrowthSafe.maxAnswerDeviation)
                (fun maxAnswerDeviation_ =>
                  Verity.bind (require (decide (deviation <= maxAnswerDeviation_)) "CAG: !deviation")
                    (fun _ =>
                      setRoundDataSafeOnlyUpTail (onlyUpWordOf s) (lastTimestampOf s)
                        dataTimestamp growthApr blockTimestamp k)))).run s).isSuccess =
          true :=
      bind_isSuccess_right_same_state
        (CustomFeedGrowthSafe.applyGrowth data growthApr dataTimestamp blockTimestamp)
        (fun __do_lift_1 =>
          Verity.bind
            (CustomFeedGrowthSafe._getDeviation (lastAnswerOf s blockTimestamp) __do_lift_1
              (onlyUpWordOf s != 0))
            (fun deviation =>
              Verity.bind (getStorage CustomFeedGrowthSafe.maxAnswerDeviation)
                (fun maxAnswerDeviation_ =>
                  Verity.bind (require (decide (deviation <= maxAnswerDeviation_)) "CAG: !deviation")
                    (fun _ =>
                      setRoundDataSafeOnlyUpTail (onlyUpWordOf s) (lastTimestampOf s)
                        dataTimestamp growthApr blockTimestamp k))))
        s (candidateLivePrice data dataTimestamp growthApr blockTimestamp) hCandidateEval
        hAfterLastAnswer
    have hDeviationSuccess :
        ((CustomFeedGrowthSafe._getDeviation (lastAnswerOf s blockTimestamp)
            (candidateLivePrice data dataTimestamp growthApr blockTimestamp)
            (onlyUpWordOf s != 0)).run s).isSuccess =
          true :=
      Verity.Proofs.Stdlib.Automation.bind_isSuccess_left _ _ _ hAfterCandidate
    cases hDeviationRun :
        ((CustomFeedGrowthSafe._getDeviation (lastAnswerOf s blockTimestamp)
            (candidateLivePrice data dataTimestamp growthApr blockTimestamp)
            (onlyUpWordOf s != 0)).run s) with
    | success deviation sDev =>
        have hDeviationSpecs :=
          getDeviation_success_implies_specs (lastAnswerOf s blockTimestamp)
            (candidateLivePrice data dataTimestamp growthApr blockTimestamp) (onlyUpWordOf s != 0)
            s sDev deviation hDeviationRun
        have hDeviationState : sDev = s := hDeviationSpecs.1
        cases hDeviationState
        have hAfterDeviation :
            ((Verity.bind (getStorage CustomFeedGrowthSafe.maxAnswerDeviation)
                (fun maxAnswerDeviation_ =>
                  Verity.bind (require (decide (deviation <= maxAnswerDeviation_)) "CAG: !deviation")
                    (fun _ =>
                      setRoundDataSafeOnlyUpTail (onlyUpWordOf s) (lastTimestampOf s)
                        dataTimestamp growthApr blockTimestamp k))).run s).isSuccess =
              true :=
          bind_isSuccess_right_same_state
            (CustomFeedGrowthSafe._getDeviation (lastAnswerOf s blockTimestamp)
              (candidateLivePrice data dataTimestamp growthApr blockTimestamp) (onlyUpWordOf s != 0))
            (fun deviation =>
              Verity.bind (getStorage CustomFeedGrowthSafe.maxAnswerDeviation)
                (fun maxAnswerDeviation_ =>
                  Verity.bind (require (decide (deviation <= maxAnswerDeviation_)) "CAG: !deviation")
                    (fun _ =>
                      setRoundDataSafeOnlyUpTail (onlyUpWordOf s) (lastTimestampOf s)
                        dataTimestamp growthApr blockTimestamp k)))
            s deviation hDeviationRun hAfterCandidate
        have hMaxEval :
            (getStorage CustomFeedGrowthSafe.maxAnswerDeviation).run s =
              ContractResult.success (maxAnswerDeviationOf s) s := by
          simp [maxAnswerDeviationOf, maxAnswerDeviationSlot, getStorage, Contract.run]
        have hAfterMax :
            ((Verity.bind (require (decide (deviation <= maxAnswerDeviationOf s)) "CAG: !deviation")
                (fun _ =>
                  setRoundDataSafeOnlyUpTail (onlyUpWordOf s) (lastTimestampOf s)
                    dataTimestamp growthApr blockTimestamp k)).run s).isSuccess =
              true :=
          bind_isSuccess_right_same_state
            (getStorage CustomFeedGrowthSafe.maxAnswerDeviation)
            (fun maxAnswerDeviation_ =>
              Verity.bind (require (decide (deviation <= maxAnswerDeviation_)) "CAG: !deviation")
                (fun _ =>
                  setRoundDataSafeOnlyUpTail (onlyUpWordOf s) (lastTimestampOf s)
                    dataTimestamp growthApr blockTimestamp k))
            s (maxAnswerDeviationOf s) hMaxEval hAfterDeviation
        have hCapRequireSuccess :
            ((require (decide (deviation <= maxAnswerDeviationOf s)) "CAG: !deviation").run s).isSuccess =
              true :=
          Verity.Proofs.Stdlib.Automation.bind_isSuccess_left _ _ _ hAfterMax
        have hCapCond : decide (deviation <= maxAnswerDeviationOf s) = true :=
          Verity.Proofs.Stdlib.Automation.require_success_implies_cond
            (decide (deviation <= maxAnswerDeviationOf s)) "CAG: !deviation" s hCapRequireSuccess
        have hCap : deviation <= maxAnswerDeviationOf s := by
          simpa using hCapCond
        have hCapRun :
            (require (decide (deviation <= maxAnswerDeviationOf s)) "CAG: !deviation").run s =
              ContractResult.success () s := by
          simp [Verity.require, hCap, Contract.run]
        have hOnlyUpTailSuccess :
            ((setRoundDataSafeOnlyUpTail (onlyUpWordOf s) (lastTimestampOf s)
                dataTimestamp growthApr blockTimestamp k).run s).isSuccess =
              true :=
          bind_isSuccess_right_same_state
            (require (decide (deviation <= maxAnswerDeviationOf s)) "CAG: !deviation")
            (fun _ =>
              setRoundDataSafeOnlyUpTail (onlyUpWordOf s) (lastTimestampOf s)
                dataTimestamp growthApr blockTimestamp k)
            s () hCapRun hAfterMax
        have hTail :=
          setRoundDataSafeOnlyUpTail_success_implies (onlyUpWordOf s) (lastTimestampOf s)
            dataTimestamp growthApr blockTimestamp s k hOnlyUpTailSuccess
        have hWithin : withinDeviationBound data dataTimestamp growthApr blockTimestamp s := by
          unfold withinDeviationBound deviationOfSafeCall
          rw [← hDeviationSpecs.2.1]
          exact hCap
        have hLastNZ :
            candidateLivePrice data dataTimestamp growthApr blockTimestamp ≠ 0 →
              (lastAnswerOf s blockTimestamp != 0) = true := by
          intro hCandidateNZ
          exact hDeviationSpecs.2.2.1 hCandidateNZ
        have hOnlyUpDeviation :
            candidateLivePrice data dataTimestamp growthApr blockTimestamp ≠ 0 →
              respectsOnlyUp data dataTimestamp growthApr blockTimestamp s := by
          intro hCandidateNZ
          unfold respectsOnlyUp
          intro hOnlyUp
          exact hDeviationSpecs.2.2.2 hCandidateNZ hOnlyUp
        have hHistoryChecks : historyChecksPass data dataTimestamp growthApr blockTimestamp s := by
          unfold historyChecksPass
          intro _hHistory
          exact ⟨hWithin, hLastNZ, hOnlyUpDeviation⟩
        exact
          ⟨hHistoryChecks, hTail.1, hTail.2.1, hTail.2.2.1, hTail.2.2.2.1,
            hTail.2.2.2.2⟩
    | _ msg sDev =>
        rw [hDeviationRun] at hDeviationSuccess
        simp [ContractResult.isSuccess] at hDeviationSuccess

private theorem setRoundDataSafe_zero_history_onlyup_off_writes
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hLastUpdated0 : lastTimestampOf s = 0)
    (hOnlyUp0 : onlyUpWordOf s = 0)
    (hTimeOrder : lastTimestampOf s <= blockTimestamp)
    (hTimeGap : sub blockTimestamp (lastTimestampOf s) > 3600)
    (hStarted : dataTimestamp > lastStartedAtOf s)
    (hDataLo : slt data (minAnswerOf s) = false)
    (hDataHi : sgt data (maxAnswerOf s) = false)
    (hGrowthLo : slt growthApr (minGrowthAprOf s) = false)
    (hGrowthHi : sgt growthApr (maxGrowthAprOf s) = false)
    (hDataTsLt : dataTimestamp < blockTimestamp)
    (storageSlot mapSlot : Nat) (k : Uint256) :
    let s' := ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd
    s'.storage storageSlot = writeStorageAfterRound s storageSlot ∧
      s'.storageMapUint mapSlot k = writeMapUintAfterRound data dataTimestamp growthApr blockTimestamp s mapSlot k := by
  have hLastUpdated0Num : s.storageMapUint 9 (s.storage 5) = 0 := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hLastUpdated0
  have hOnlyUp0Num : s.storage 6 = 0 := by
    simpa [onlyUpWordOf, onlyUpSlot] using hOnlyUp0
  have hDataLoNum : slt data (s.storage 1) = false := by simpa [minAnswerOf, minAnswerSlot] using hDataLo
  have hDataHiNum : sgt data (s.storage 2) = false := by simpa [maxAnswerOf, maxAnswerSlot] using hDataHi
  have hGrowthLoNum : slt growthApr (s.storage 3) = false := by
    simpa [minGrowthAprOf, minGrowthAprSlot] using hGrowthLo
  have hGrowthHiNum : sgt growthApr (s.storage 4) = false := by
    simpa [maxGrowthAprOf, maxGrowthAprSlot] using hGrowthHi
  have hLastUpdatedBranch :
      ¬ ((s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
            (s.storage CustomFeedGrowthSafe.latestRound.slot) != 0) =
          true) := by
    simpa [latestRoundSlot, roundUpdatedAtSlot, hLastUpdated0Num]
  have hOnlyUpBranch : ¬ ((s.storage CustomFeedGrowthSafe.onlyUp.slot != 0) = true) := by
    simpa [onlyUpSlot, hOnlyUp0Num]
  have hDataLoBranch : ¬ (slt data (s.storage CustomFeedGrowthSafe.minAnswer.slot) = true) := by
    simpa [minAnswerSlot, hDataLoNum]
  have hDataHiBranch : ¬ (sgt data (s.storage CustomFeedGrowthSafe.maxAnswer.slot) = true) := by
    simpa [maxAnswerSlot, hDataHiNum]
  have hGrowthLoBranch :
      ¬ (slt growthApr (s.storage CustomFeedGrowthSafe.minGrowthApr.slot) = true) := by
    simpa [minGrowthAprSlot, hGrowthLoNum]
  have hGrowthHiBranch :
      ¬ (sgt growthApr (s.storage CustomFeedGrowthSafe.maxGrowthApr.slot) = true) := by
    simpa [maxGrowthAprSlot, hGrowthHiNum]
  have hTimestampUnderflowProp :
      s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot) ≤
        blockTimestamp := by
    simpa [latestRoundSlot, roundUpdatedAtSlot, hLastUpdated0Num]
  have hTimestampUnderflowVal : (s.storageMapUint 9 (s.storage 5)).val ≤ blockTimestamp.val := by
    simpa [latestRoundSlot, roundUpdatedAtSlot, hLastUpdated0Num]
  have hTimestampUnderflowValProp :
      (s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot)).val ≤
        blockTimestamp.val := by
    simpa [latestRoundSlot, roundUpdatedAtSlot] using hTimestampUnderflowVal
  have hTimeGapProp :
      sub blockTimestamp
          (s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
            (s.storage CustomFeedGrowthSafe.latestRound.slot)) >
        3600 := by
    simpa [hLastUpdated0, lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot]
      using hTimeGap
  have hTimeGapVal : Core.Uint256.val 3600 < (sub blockTimestamp (s.storageMapUint 9 (s.storage 5))).val := by
    simpa [hLastUpdated0, lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot]
      using hTimeGap
  have hTimeGapValProp :
      Core.Uint256.val 3600 <
        (sub blockTimestamp
          (s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
            (s.storage CustomFeedGrowthSafe.latestRound.slot))).val := by
    simpa [latestRoundSlot, roundUpdatedAtSlot] using hTimeGapVal
  have hStartedProp :
      dataTimestamp >
        s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot) := by
    simpa [latestRoundSlot, roundStartedAtSlot] using hStarted
  have hStartedVal : (s.storageMapUint 8 (s.storage 5)).val < dataTimestamp.val := by
    simpa [latestRoundSlot, roundStartedAtSlot] using hStarted
  have hStartedValProp :
      (s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot)).val <
        dataTimestamp.val := by
    simpa [latestRoundSlot, roundStartedAtSlot] using hStartedVal
  let _ := hTimeOrder
  have hSafeEq :
      ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd =
        ((CustomFeedGrowthSafe.setRoundData data dataTimestamp growthApr blockTimestamp).run s).snd := by
    unfold CustomFeedGrowthSafe.setRoundDataSafe Verity.require
    simp [Verity.require, getStorage, getMappingUint, setStorage, setMappingUint, Verity.bind, Bind.bind, Pure.pure, Contract.run,
      ContractResult.snd, CustomFeedGrowthSafe.lastTimestamp, CustomFeedGrowthSafe.lastStartedAt,
      CustomFeedGrowthSafe.lastRawAnswer, CustomFeedGrowthSafe.lastGrowthApr,
      CustomFeedGrowthSafe.lastAnswer, CustomFeedGrowthSafe.applyGrowth,
      CustomFeedGrowthSafe.applyGrowthAt, CustomFeedGrowthSafe._getDeviation,
      CustomFeedGrowthSafe.setRoundData, hLastUpdatedBranch, hOnlyUpBranch, hDataLoBranch, hDataHiBranch,
      hGrowthLoBranch, hGrowthHiBranch, hTimestampUnderflowProp, hTimestampUnderflowVal,
      hTimestampUnderflowValProp, hTimeGapProp, hTimeGapVal, hTimeGapValProp, hStartedProp,
      hStartedVal, hStartedValProp, hDataTsLt]
  constructor
  · rw [hSafeEq]
    simpa using
      (setRoundData_writes data dataTimestamp growthApr blockTimestamp s
        hDataLoBranch hDataHiBranch hGrowthLoBranch hGrowthHiBranch hDataTsLt storageSlot mapSlot k).1
  · rw [hSafeEq]
    simpa using
      (setRoundData_writes data dataTimestamp growthApr blockTimestamp s
        hDataLoBranch hDataHiBranch hGrowthLoBranch hGrowthHiBranch hDataTsLt storageSlot mapSlot k).2

private theorem setRoundDataSafe_zero_history_onlyup_on_writes
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hLastUpdated0 : lastTimestampOf s = 0)
    (hOnlyUp0 : ¬ onlyUpWordOf s = 0)
    (hOnlyUpApr : slt growthApr 0 = false)
    (hTimeOrder : lastTimestampOf s <= blockTimestamp)
    (hTimeGap : sub blockTimestamp (lastTimestampOf s) > 3600)
    (hStarted : dataTimestamp > lastStartedAtOf s)
    (hDataLo : slt data (minAnswerOf s) = false)
    (hDataHi : sgt data (maxAnswerOf s) = false)
    (hGrowthLo : slt growthApr (minGrowthAprOf s) = false)
    (hGrowthHi : sgt growthApr (maxGrowthAprOf s) = false)
    (hDataTsLt : dataTimestamp < blockTimestamp)
    (storageSlot mapSlot : Nat) (k : Uint256) :
    let s' := ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd
    s'.storage storageSlot = writeStorageAfterRound s storageSlot ∧
      s'.storageMapUint mapSlot k = writeMapUintAfterRound data dataTimestamp growthApr blockTimestamp s mapSlot k := by
  have hLastUpdated0Num : s.storageMapUint 9 (s.storage 5) = 0 := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hLastUpdated0
  have hOnlyUp0Num : s.storage 6 ≠ 0 := by
    simpa [onlyUpWordOf, onlyUpSlot] using hOnlyUp0
  have hDataLoNum : slt data (s.storage 1) = false := by simpa [minAnswerOf, minAnswerSlot] using hDataLo
  have hDataHiNum : sgt data (s.storage 2) = false := by simpa [maxAnswerOf, maxAnswerSlot] using hDataHi
  have hGrowthLoNum : slt growthApr (s.storage 3) = false := by
    simpa [minGrowthAprOf, minGrowthAprSlot] using hGrowthLo
  have hGrowthHiNum : sgt growthApr (s.storage 4) = false := by
    simpa [maxGrowthAprOf, maxGrowthAprSlot] using hGrowthHi
  have hLastUpdatedBranch :
      ¬ ((s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
            (s.storage CustomFeedGrowthSafe.latestRound.slot) != 0) =
          true) := by
    simpa [latestRoundSlot, roundUpdatedAtSlot, hLastUpdated0Num]
  have hOnlyUpBranch : ((s.storage CustomFeedGrowthSafe.onlyUp.slot != 0) = true) := by
    simpa [onlyUpSlot, hOnlyUp0Num]
  have hOnlyUpAprBranch : ¬ (slt growthApr 0 = true) := by simpa [hOnlyUpApr]
  have hDataLoBranch : ¬ (slt data (s.storage CustomFeedGrowthSafe.minAnswer.slot) = true) := by
    simpa [minAnswerSlot, hDataLoNum]
  have hDataHiBranch : ¬ (sgt data (s.storage CustomFeedGrowthSafe.maxAnswer.slot) = true) := by
    simpa [maxAnswerSlot, hDataHiNum]
  have hGrowthLoBranch :
      ¬ (slt growthApr (s.storage CustomFeedGrowthSafe.minGrowthApr.slot) = true) := by
    simpa [minGrowthAprSlot, hGrowthLoNum]
  have hGrowthHiBranch :
      ¬ (sgt growthApr (s.storage CustomFeedGrowthSafe.maxGrowthApr.slot) = true) := by
    simpa [maxGrowthAprSlot, hGrowthHiNum]
  have hTimestampUnderflowProp :
      s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot) ≤
        blockTimestamp := by
    simpa [latestRoundSlot, roundUpdatedAtSlot, hLastUpdated0Num]
  have hTimestampUnderflowVal : (s.storageMapUint 9 (s.storage 5)).val ≤ blockTimestamp.val := by
    simpa [latestRoundSlot, roundUpdatedAtSlot, hLastUpdated0Num]
  have hTimestampUnderflowValProp :
      (s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot)).val ≤
        blockTimestamp.val := by
    simpa [latestRoundSlot, roundUpdatedAtSlot] using hTimestampUnderflowVal
  have hTimeGapProp :
      sub blockTimestamp
          (s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
            (s.storage CustomFeedGrowthSafe.latestRound.slot)) >
        3600 := by
    simpa [hLastUpdated0, lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot]
      using hTimeGap
  have hTimeGapVal : Core.Uint256.val 3600 < (sub blockTimestamp (s.storageMapUint 9 (s.storage 5))).val := by
    simpa [hLastUpdated0, lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot]
      using hTimeGap
  have hTimeGapValProp :
      Core.Uint256.val 3600 <
        (sub blockTimestamp
          (s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
            (s.storage CustomFeedGrowthSafe.latestRound.slot))).val := by
    simpa [latestRoundSlot, roundUpdatedAtSlot] using hTimeGapVal
  have hStartedProp :
      dataTimestamp >
        s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot) := by
    simpa [latestRoundSlot, roundStartedAtSlot] using hStarted
  have hStartedVal : (s.storageMapUint 8 (s.storage 5)).val < dataTimestamp.val := by
    simpa [latestRoundSlot, roundStartedAtSlot] using hStarted
  have hStartedValProp :
      (s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot)).val <
        dataTimestamp.val := by
    simpa [latestRoundSlot, roundStartedAtSlot] using hStartedVal
  let _ := hTimeOrder
  have hSafeEq :
      ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd =
        ((CustomFeedGrowthSafe.setRoundData data dataTimestamp growthApr blockTimestamp).run s).snd := by
    unfold CustomFeedGrowthSafe.setRoundDataSafe Verity.require
    simp [Verity.require, getStorage, getMappingUint, setStorage, setMappingUint, Verity.bind, Bind.bind, Pure.pure, Contract.run,
      ContractResult.snd, CustomFeedGrowthSafe.lastTimestamp, CustomFeedGrowthSafe.lastStartedAt,
      CustomFeedGrowthSafe.lastRawAnswer, CustomFeedGrowthSafe.lastGrowthApr,
      CustomFeedGrowthSafe.lastAnswer, CustomFeedGrowthSafe.applyGrowth,
      CustomFeedGrowthSafe.applyGrowthAt, CustomFeedGrowthSafe._getDeviation,
      CustomFeedGrowthSafe.setRoundData, hLastUpdatedBranch, hOnlyUpBranch, hOnlyUpAprBranch, hDataLoBranch,
      hDataHiBranch, hGrowthLoBranch, hGrowthHiBranch, hTimestampUnderflowProp, hTimestampUnderflowVal,
      hTimestampUnderflowValProp, hTimeGapProp, hTimeGapVal, hTimeGapValProp, hStartedProp, hStartedVal,
      hStartedValProp, hDataTsLt]
  constructor
  · rw [hSafeEq]
    simpa using
      (setRoundData_writes data dataTimestamp growthApr blockTimestamp s
        hDataLoBranch hDataHiBranch hGrowthLoBranch hGrowthHiBranch hDataTsLt storageSlot mapSlot k).1
  · rw [hSafeEq]
    simpa using
      (setRoundData_writes data dataTimestamp growthApr blockTimestamp s
        hDataLoBranch hDataHiBranch hGrowthLoBranch hGrowthHiBranch hDataTsLt storageSlot mapSlot k).2

private theorem setRoundDataSafe_candidate_zero_onlyup_off_writes
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hLastUpdated0 : ¬ lastTimestampOf s = 0)
    (hPrevStarted : lastStartedAtOf s <= blockTimestamp)
    (hDataTsLe : dataTimestamp <= blockTimestamp)
    (hDeviationCap :
      deviationOfSafeCall data dataTimestamp growthApr blockTimestamp s <= maxAnswerDeviationOf s)
    (hCandidateZero : candidateLivePrice data dataTimestamp growthApr blockTimestamp = 0)
    (hOnlyUp0 : onlyUpWordOf s = 0)
    (hTimeOrder : lastTimestampOf s <= blockTimestamp)
    (hTimeGap : sub blockTimestamp (lastTimestampOf s) > 3600)
    (hStarted : dataTimestamp > lastStartedAtOf s)
    (hDataLo : slt data (minAnswerOf s) = false)
    (hDataHi : sgt data (maxAnswerOf s) = false)
    (hGrowthLo : slt growthApr (minGrowthAprOf s) = false)
    (hGrowthHi : sgt growthApr (maxGrowthAprOf s) = false)
    (hDataTsLt : dataTimestamp < blockTimestamp)
    (storageSlot mapSlot : Nat) (k : Uint256) :
    let s' := ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd
    s'.storage storageSlot = writeStorageAfterRound s storageSlot ∧
      s'.storageMapUint mapSlot k = writeMapUintAfterRound data dataTimestamp growthApr blockTimestamp s mapSlot k := by
  have hLastUpdatedNZNum : s.storageMapUint 9 (s.storage 5) ≠ 0 := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hLastUpdated0
  have hCandidateZeroNum :
      add data (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr) 315360000000000000) = 0 := by
    simpa [candidateLivePrice, applyGrowthNowRaw, applyGrowthAtRaw] using hCandidateZero
  have hCandidateZeroDenom :
      add data (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr) GROWTH_DENOMINATOR) = 0 := by
    simpa [GROWTH_DENOMINATOR, HUNDRED_ONE, ONE, YEAR_SECONDS] using hCandidateZeroNum
  have hZeroDeviationCapNum : 10000000000 <= s.storage 0 := by
    have hZeroDeviationCapRaw :
        (if
              add data (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr) GROWTH_DENOMINATOR) = 0 then
            (mul 100 ONE).val
          else
            (absSignedWord
                (signedDeviationRaw (lastAnswerOf s blockTimestamp)
                  (add data
                    (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr) GROWTH_DENOMINATOR)))).val) ≤
          (s.storage 0).val := by
      simpa [deviationOfSafeCall, candidateLivePrice, applyGrowthNowRaw, applyGrowthAtRaw,
        deviationAbsRaw, maxAnswerDeviationOf] using hDeviationCap
    simpa [HUNDRED_ONE, ONE, hCandidateZeroDenom] using hZeroDeviationCapRaw
  have hOnlyUp0Num : s.storage 6 = 0 := by simpa [onlyUpWordOf, onlyUpSlot] using hOnlyUp0
  have hDataLoNum : slt data (s.storage 1) = false := by simpa [minAnswerOf, minAnswerSlot] using hDataLo
  have hDataHiNum : sgt data (s.storage 2) = false := by simpa [maxAnswerOf, maxAnswerSlot] using hDataHi
  have hGrowthLoNum : slt growthApr (s.storage 3) = false := by
    simpa [minGrowthAprOf, minGrowthAprSlot] using hGrowthLo
  have hGrowthHiNum : sgt growthApr (s.storage 4) = false := by
    simpa [maxGrowthAprOf, maxGrowthAprSlot] using hGrowthHi
  have hLastUpdatedBranch :
      ((s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
            (s.storage CustomFeedGrowthSafe.latestRound.slot) != 0) =
          true) := by
    simpa [latestRoundSlot, roundUpdatedAtSlot, hLastUpdatedNZNum]
  have hCandidateZeroBranch :
      ((add data
            (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr) 315360000000000000) ==
          0) =
        true) := by
    simpa [hCandidateZeroNum]
  have hOnlyUpBranch : ¬ ((s.storage CustomFeedGrowthSafe.onlyUp.slot != 0) = true) := by
    simpa [onlyUpSlot, hOnlyUp0Num]
  have hDataLoBranch : ¬ (slt data (s.storage CustomFeedGrowthSafe.minAnswer.slot) = true) := by
    simpa [minAnswerSlot, hDataLoNum]
  have hDataHiBranch : ¬ (sgt data (s.storage CustomFeedGrowthSafe.maxAnswer.slot) = true) := by
    simpa [maxAnswerSlot, hDataHiNum]
  have hGrowthLoBranch :
      ¬ (slt growthApr (s.storage CustomFeedGrowthSafe.minGrowthApr.slot) = true) := by
    simpa [minGrowthAprSlot, hGrowthLoNum]
  have hGrowthHiBranch :
      ¬ (sgt growthApr (s.storage CustomFeedGrowthSafe.maxGrowthApr.slot) = true) := by
    simpa [maxGrowthAprSlot, hGrowthHiNum]
  have hPrevStartedProp :
      s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot) ≤
        blockTimestamp := by
    simpa [latestRoundSlot, roundStartedAtSlot] using hPrevStarted
  have hPrevStartedVal :
      (s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot)).val ≤
        blockTimestamp.val := by
    simpa [lastStartedAtOf, roundStartedAtOf, latestRoundOf, latestRoundSlot, roundStartedAtSlot] using
      hPrevStarted
  have hDataTsLeVal : dataTimestamp.val ≤ blockTimestamp.val := by
    simpa using hDataTsLe
  have hZeroDeviationCapProp :
      10000000000 ≤ s.storage CustomFeedGrowthSafe.maxAnswerDeviation.slot := by
    simpa [maxAnswerDeviationSlot] using hZeroDeviationCapNum
  have hZeroDeviationCapVal :
      HUNDRED_ONE.val ≤ (s.storage CustomFeedGrowthSafe.maxAnswerDeviation.slot).val := by
    simpa [HUNDRED_ONE, ONE, maxAnswerDeviationSlot] using hZeroDeviationCapNum
  have hTimestampUnderflowProp :
      s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot) ≤
        blockTimestamp := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hTimeOrder
  have hTimestampUnderflowVal : (s.storageMapUint 9 (s.storage 5)).val ≤ blockTimestamp.val := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hTimeOrder
  have hTimestampUnderflowValProp :
      (s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot)).val ≤
        blockTimestamp.val := by
    simpa [latestRoundSlot, roundUpdatedAtSlot] using hTimestampUnderflowVal
  have hTimeGapProp :
      sub blockTimestamp
          (s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
            (s.storage CustomFeedGrowthSafe.latestRound.slot)) >
        3600 := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hTimeGap
  have hTimeGapVal : Core.Uint256.val 3600 < (sub blockTimestamp (s.storageMapUint 9 (s.storage 5))).val := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hTimeGap
  have hTimeGapValProp :
      Core.Uint256.val 3600 <
        (sub blockTimestamp
          (s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
            (s.storage CustomFeedGrowthSafe.latestRound.slot))).val := by
    simpa [latestRoundSlot, roundUpdatedAtSlot] using hTimeGapVal
  have hStartedProp :
      dataTimestamp >
        s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot) := by
    simpa [lastStartedAtOf, roundStartedAtOf, latestRoundOf, latestRoundSlot, roundStartedAtSlot] using
      hStarted
  have hStartedVal : (s.storageMapUint 8 (s.storage 5)).val < dataTimestamp.val := by
    simpa [lastStartedAtOf, roundStartedAtOf, latestRoundOf, latestRoundSlot, roundStartedAtSlot] using
      hStarted
  have hStartedValProp :
      (s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot)).val <
        dataTimestamp.val := by
    simpa [latestRoundSlot, roundStartedAtSlot] using hStartedVal
  have hSafeEq :
      ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd =
        ((CustomFeedGrowthSafe.setRoundData data dataTimestamp growthApr blockTimestamp).run s).snd := by
    unfold CustomFeedGrowthSafe.setRoundDataSafe Verity.require
    simp [Verity.require, getStorage, getMappingUint, setStorage, setMappingUint, Verity.bind, Bind.bind, Pure.pure, Contract.run,
      ContractResult.snd, CustomFeedGrowthSafe.lastTimestamp, CustomFeedGrowthSafe.lastStartedAt,
      CustomFeedGrowthSafe.lastRawAnswer, CustomFeedGrowthSafe.lastGrowthApr,
      CustomFeedGrowthSafe.lastAnswer, CustomFeedGrowthSafe.applyGrowth,
      CustomFeedGrowthSafe.applyGrowthAt, CustomFeedGrowthSafe._getDeviation,
      CustomFeedGrowthSafe.setRoundData, hLastUpdatedBranch, hCandidateZeroBranch, hCandidateZeroDenom,
      hOnlyUpBranch, hPrevStartedProp, hPrevStartedVal, hDataTsLe, hDataTsLeVal, hZeroDeviationCapProp,
      hZeroDeviationCapVal,
      hTimestampUnderflowProp, hTimestampUnderflowVal, hTimestampUnderflowValProp, hTimeGapProp, hTimeGapVal,
      hTimeGapValProp, hStartedProp, hStartedVal, hStartedValProp, hDataLoBranch, hDataHiBranch,
      hGrowthLoBranch, hGrowthHiBranch, hDataTsLt]
  constructor
  · rw [hSafeEq]
    simpa using
      (setRoundData_writes data dataTimestamp growthApr blockTimestamp s
        hDataLoBranch hDataHiBranch hGrowthLoBranch hGrowthHiBranch hDataTsLt storageSlot mapSlot k).1
  · rw [hSafeEq]
    simpa using
      (setRoundData_writes data dataTimestamp growthApr blockTimestamp s
        hDataLoBranch hDataHiBranch hGrowthLoBranch hGrowthHiBranch hDataTsLt storageSlot mapSlot k).2

private theorem setRoundDataSafe_candidate_zero_onlyup_on_writes
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hLastUpdated0 : ¬ lastTimestampOf s = 0)
    (hPrevStarted : lastStartedAtOf s <= blockTimestamp)
    (hDataTsLe : dataTimestamp <= blockTimestamp)
    (hDeviationCap :
      deviationOfSafeCall data dataTimestamp growthApr blockTimestamp s <= maxAnswerDeviationOf s)
    (hCandidateZero : candidateLivePrice data dataTimestamp growthApr blockTimestamp = 0)
    (hOnlyUp0 : ¬ onlyUpWordOf s = 0)
    (hOnlyUpApr : slt growthApr 0 = false)
    (hTimeOrder : lastTimestampOf s <= blockTimestamp)
    (hTimeGap : sub blockTimestamp (lastTimestampOf s) > 3600)
    (hStarted : dataTimestamp > lastStartedAtOf s)
    (hDataLo : slt data (minAnswerOf s) = false)
    (hDataHi : sgt data (maxAnswerOf s) = false)
    (hGrowthLo : slt growthApr (minGrowthAprOf s) = false)
    (hGrowthHi : sgt growthApr (maxGrowthAprOf s) = false)
    (hDataTsLt : dataTimestamp < blockTimestamp)
    (storageSlot mapSlot : Nat) (k : Uint256) :
    let s' := ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd
    s'.storage storageSlot = writeStorageAfterRound s storageSlot ∧
      s'.storageMapUint mapSlot k = writeMapUintAfterRound data dataTimestamp growthApr blockTimestamp s mapSlot k := by
  have hLastUpdatedNZNum : s.storageMapUint 9 (s.storage 5) ≠ 0 := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hLastUpdated0
  have hCandidateZeroNum :
      add data (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr) 315360000000000000) = 0 := by
    simpa [candidateLivePrice, applyGrowthNowRaw, applyGrowthAtRaw] using hCandidateZero
  have hCandidateZeroDenom :
      add data (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr) GROWTH_DENOMINATOR) = 0 := by
    simpa [GROWTH_DENOMINATOR, HUNDRED_ONE, ONE, YEAR_SECONDS] using hCandidateZeroNum
  have hZeroDeviationCapNum : 10000000000 <= s.storage 0 := by
    have hZeroDeviationCapRaw :
        (if
              add data (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr) GROWTH_DENOMINATOR) = 0 then
            (mul 100 ONE).val
          else
            (absSignedWord
                (signedDeviationRaw (lastAnswerOf s blockTimestamp)
                  (add data
                    (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr) GROWTH_DENOMINATOR)))).val) ≤
          (s.storage 0).val := by
      simpa [deviationOfSafeCall, candidateLivePrice, applyGrowthNowRaw, applyGrowthAtRaw,
        deviationAbsRaw, maxAnswerDeviationOf] using hDeviationCap
    simpa [HUNDRED_ONE, ONE, hCandidateZeroDenom] using hZeroDeviationCapRaw
  have hOnlyUp0Num : s.storage 6 ≠ 0 := by simpa [onlyUpWordOf, onlyUpSlot] using hOnlyUp0
  have hDataLoNum : slt data (s.storage 1) = false := by simpa [minAnswerOf, minAnswerSlot] using hDataLo
  have hDataHiNum : sgt data (s.storage 2) = false := by simpa [maxAnswerOf, maxAnswerSlot] using hDataHi
  have hGrowthLoNum : slt growthApr (s.storage 3) = false := by
    simpa [minGrowthAprOf, minGrowthAprSlot] using hGrowthLo
  have hGrowthHiNum : sgt growthApr (s.storage 4) = false := by
    simpa [maxGrowthAprOf, maxGrowthAprSlot] using hGrowthHi
  have hLastUpdatedBranch :
      ((s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
            (s.storage CustomFeedGrowthSafe.latestRound.slot) != 0) =
          true) := by
    simpa [latestRoundSlot, roundUpdatedAtSlot, hLastUpdatedNZNum]
  have hCandidateZeroBranch :
      ((add data
            (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr) 315360000000000000) ==
          0) =
        true) := by
    simpa [hCandidateZeroNum]
  have hOnlyUpBranch : ((s.storage CustomFeedGrowthSafe.onlyUp.slot != 0) = true) := by
    simpa [onlyUpSlot, hOnlyUp0Num]
  have hOnlyUpAprBranch : ¬ (slt growthApr 0 = true) := by simpa [hOnlyUpApr]
  have hDataLoBranch : ¬ (slt data (s.storage CustomFeedGrowthSafe.minAnswer.slot) = true) := by
    simpa [minAnswerSlot, hDataLoNum]
  have hDataHiBranch : ¬ (sgt data (s.storage CustomFeedGrowthSafe.maxAnswer.slot) = true) := by
    simpa [maxAnswerSlot, hDataHiNum]
  have hGrowthLoBranch :
      ¬ (slt growthApr (s.storage CustomFeedGrowthSafe.minGrowthApr.slot) = true) := by
    simpa [minGrowthAprSlot, hGrowthLoNum]
  have hGrowthHiBranch :
      ¬ (sgt growthApr (s.storage CustomFeedGrowthSafe.maxGrowthApr.slot) = true) := by
    simpa [maxGrowthAprSlot, hGrowthHiNum]
  have hPrevStartedProp :
      s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot) ≤
        blockTimestamp := by
    simpa [latestRoundSlot, roundStartedAtSlot] using hPrevStarted
  have hPrevStartedVal :
      (s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot)).val ≤
        blockTimestamp.val := by
    simpa [lastStartedAtOf, roundStartedAtOf, latestRoundOf, latestRoundSlot, roundStartedAtSlot] using
      hPrevStarted
  have hDataTsLeVal : dataTimestamp.val ≤ blockTimestamp.val := by
    simpa using hDataTsLe
  have hZeroDeviationCapProp :
      10000000000 ≤ s.storage CustomFeedGrowthSafe.maxAnswerDeviation.slot := by
    simpa [maxAnswerDeviationSlot] using hZeroDeviationCapNum
  have hZeroDeviationCapVal :
      HUNDRED_ONE.val ≤ (s.storage CustomFeedGrowthSafe.maxAnswerDeviation.slot).val := by
    simpa [HUNDRED_ONE, ONE, maxAnswerDeviationSlot] using hZeroDeviationCapNum
  have hTimestampUnderflowProp :
      s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot) ≤
        blockTimestamp := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hTimeOrder
  have hTimestampUnderflowVal : (s.storageMapUint 9 (s.storage 5)).val ≤ blockTimestamp.val := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hTimeOrder
  have hTimestampUnderflowValProp :
      (s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot)).val ≤
        blockTimestamp.val := by
    simpa [latestRoundSlot, roundUpdatedAtSlot] using hTimestampUnderflowVal
  have hTimeGapProp :
      sub blockTimestamp
          (s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
            (s.storage CustomFeedGrowthSafe.latestRound.slot)) >
        3600 := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hTimeGap
  have hTimeGapVal : Core.Uint256.val 3600 < (sub blockTimestamp (s.storageMapUint 9 (s.storage 5))).val := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hTimeGap
  have hTimeGapValProp :
      Core.Uint256.val 3600 <
        (sub blockTimestamp
          (s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
            (s.storage CustomFeedGrowthSafe.latestRound.slot))).val := by
    simpa [latestRoundSlot, roundUpdatedAtSlot] using hTimeGapVal
  have hStartedProp :
      dataTimestamp >
        s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot) := by
    simpa [lastStartedAtOf, roundStartedAtOf, latestRoundOf, latestRoundSlot, roundStartedAtSlot] using
      hStarted
  have hStartedVal : (s.storageMapUint 8 (s.storage 5)).val < dataTimestamp.val := by
    simpa [lastStartedAtOf, roundStartedAtOf, latestRoundOf, latestRoundSlot, roundStartedAtSlot] using
      hStarted
  have hStartedValProp :
      (s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot)).val <
        dataTimestamp.val := by
    simpa [latestRoundSlot, roundStartedAtSlot] using hStartedVal
  have hSafeEq :
      ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd =
        ((CustomFeedGrowthSafe.setRoundData data dataTimestamp growthApr blockTimestamp).run s).snd := by
    unfold CustomFeedGrowthSafe.setRoundDataSafe Verity.require
    simp [Verity.require, getStorage, getMappingUint, setStorage, setMappingUint, Verity.bind, Bind.bind, Pure.pure, Contract.run,
      ContractResult.snd, CustomFeedGrowthSafe.lastTimestamp, CustomFeedGrowthSafe.lastStartedAt,
      CustomFeedGrowthSafe.lastRawAnswer, CustomFeedGrowthSafe.lastGrowthApr,
      CustomFeedGrowthSafe.lastAnswer, CustomFeedGrowthSafe.applyGrowth,
      CustomFeedGrowthSafe.applyGrowthAt, CustomFeedGrowthSafe._getDeviation,
      CustomFeedGrowthSafe.setRoundData, hLastUpdatedBranch, hCandidateZeroBranch, hCandidateZeroDenom,
      hOnlyUpBranch, hOnlyUpAprBranch, hPrevStartedProp, hPrevStartedVal, hDataTsLe, hDataTsLeVal,
      hZeroDeviationCapProp, hZeroDeviationCapVal,
      hTimestampUnderflowProp, hTimestampUnderflowVal, hTimestampUnderflowValProp, hTimeGapProp, hTimeGapVal,
      hTimeGapValProp, hStartedProp, hStartedVal, hStartedValProp, hDataLoBranch, hDataHiBranch,
      hGrowthLoBranch, hGrowthHiBranch, hDataTsLt]
  constructor
  · rw [hSafeEq]
    simpa using
      (setRoundData_writes data dataTimestamp growthApr blockTimestamp s
        hDataLoBranch hDataHiBranch hGrowthLoBranch hGrowthHiBranch hDataTsLt storageSlot mapSlot k).1
  · rw [hSafeEq]
    simpa using
      (setRoundData_writes data dataTimestamp growthApr blockTimestamp s
        hDataLoBranch hDataHiBranch hGrowthLoBranch hGrowthHiBranch hDataTsLt storageSlot mapSlot k).2

private theorem setRoundDataSafe_candidate_nonzero_onlyup_off_writes
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hLastUpdated0 : ¬ lastTimestampOf s = 0)
    (hPrevStarted : lastStartedAtOf s <= blockTimestamp)
    (hDataTsLe : dataTimestamp <= blockTimestamp)
    (hLastAnswerNZ : lastAnswerOf s blockTimestamp != 0)
    (hDeviationCap :
      deviationOfSafeCall data dataTimestamp growthApr blockTimestamp s <= maxAnswerDeviationOf s)
    (hCandidateZero : ¬ candidateLivePrice data dataTimestamp growthApr blockTimestamp = 0)
    (hOnlyUp0 : onlyUpWordOf s = 0)
    (hTimeOrder : lastTimestampOf s <= blockTimestamp)
    (hTimeGap : sub blockTimestamp (lastTimestampOf s) > 3600)
    (hStarted : dataTimestamp > lastStartedAtOf s)
    (hDataLo : slt data (minAnswerOf s) = false)
    (hDataHi : sgt data (maxAnswerOf s) = false)
    (hGrowthLo : slt growthApr (minGrowthAprOf s) = false)
    (hGrowthHi : sgt growthApr (maxGrowthAprOf s) = false)
    (hDataTsLt : dataTimestamp < blockTimestamp)
    (storageSlot mapSlot : Nat) (k : Uint256) :
    let s' := ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd
    s'.storage storageSlot = writeStorageAfterRound s storageSlot ∧
      s'.storageMapUint mapSlot k = writeMapUintAfterRound data dataTimestamp growthApr blockTimestamp s mapSlot k := by
  have hLastUpdatedNZNum : s.storageMapUint 9 (s.storage 5) ≠ 0 := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hLastUpdated0
  have hOnlyUp0Num : s.storage 6 = 0 := by simpa [onlyUpWordOf, onlyUpSlot] using hOnlyUp0
  have hDataLoNum : slt data (s.storage 1) = false := by simpa [minAnswerOf, minAnswerSlot] using hDataLo
  have hDataHiNum : sgt data (s.storage 2) = false := by simpa [maxAnswerOf, maxAnswerSlot] using hDataHi
  have hGrowthLoNum : slt growthApr (s.storage 3) = false := by
    simpa [minGrowthAprOf, minGrowthAprSlot] using hGrowthLo
  have hGrowthHiNum : sgt growthApr (s.storage 4) = false := by
    simpa [maxGrowthAprOf, maxGrowthAprSlot] using hGrowthHi
  have hCandidateNZNum :
      add data (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr) 315360000000000000) ≠ 0 := by
    simpa [candidateLivePrice, applyGrowthNowRaw, applyGrowthAtRaw] using hCandidateZero
  have hCandidateNZDenom :
      add data (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr) GROWTH_DENOMINATOR) ≠ 0 := by
    simpa [GROWTH_DENOMINATOR, HUNDRED_ONE, ONE, YEAR_SECONDS] using hCandidateNZNum
  have hLastAnswerNZNum :
      add (s.storageMapUint 7 (s.storage 5))
          (sdiv
            (mul
              (mul (s.storageMapUint 7 (s.storage 5))
                (sub blockTimestamp (s.storageMapUint 8 (s.storage 5))))
              (s.storageMapUint 10 (s.storage 5)))
            315360000000000000) ≠ 0 := by
    simpa [lastAnswerOf, applyGrowthNowRaw, applyGrowthAtRaw,
      lastRawAnswerOf, lastStartedAtOf, lastGrowthAprOf,
      roundAnswerOf, roundStartedAtOf, roundGrowthAprOf, latestRoundOf,
      latestRoundSlot, roundAnswerSlot, roundStartedAtSlot, roundGrowthAprSlot] using hLastAnswerNZ
  have hLastUpdatedBranch :
      ((s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
            (s.storage CustomFeedGrowthSafe.latestRound.slot) != 0) =
          true) := by
    simpa [latestRoundSlot, roundUpdatedAtSlot, hLastUpdatedNZNum]
  have hCandidateZeroBranch :
      ¬ ((add data
              (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr) 315360000000000000) ==
            0) =
          true) := by
    simp [hCandidateNZNum]
  have hLastAnswerNZBranch :
      ((add
              (s.storageMapUint CustomFeedGrowthSafe.roundAnswer.slot
                (s.storage CustomFeedGrowthSafe.latestRound.slot))
              (sdiv
                (mul
                  (mul
                    (s.storageMapUint CustomFeedGrowthSafe.roundAnswer.slot
                      (s.storage CustomFeedGrowthSafe.latestRound.slot))
                    (sub blockTimestamp
                      (s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
                        (s.storage CustomFeedGrowthSafe.latestRound.slot))))
                  (s.storageMapUint CustomFeedGrowthSafe.roundGrowthApr.slot
                    (s.storage CustomFeedGrowthSafe.latestRound.slot)))
                315360000000000000) !=
            0) =
        true) := by
    simpa [latestRoundSlot, roundAnswerSlot, roundStartedAtSlot, roundGrowthAprSlot, hLastAnswerNZNum]
  have hOnlyUpBranch : ¬ ((s.storage CustomFeedGrowthSafe.onlyUp.slot != 0) = true) := by
    simpa [onlyUpSlot, hOnlyUp0Num]
  have hDataLoBranch : ¬ (slt data (s.storage CustomFeedGrowthSafe.minAnswer.slot) = true) := by
    simpa [minAnswerSlot, hDataLoNum]
  have hDataHiBranch : ¬ (sgt data (s.storage CustomFeedGrowthSafe.maxAnswer.slot) = true) := by
    simpa [maxAnswerSlot, hDataHiNum]
  have hGrowthLoBranch :
      ¬ (slt growthApr (s.storage CustomFeedGrowthSafe.minGrowthApr.slot) = true) := by
    simpa [minGrowthAprSlot, hGrowthLoNum]
  have hGrowthHiBranch :
      ¬ (sgt growthApr (s.storage CustomFeedGrowthSafe.maxGrowthApr.slot) = true) := by
    simpa [maxGrowthAprSlot, hGrowthHiNum]
  have hPrevStartedProp :
      s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot) ≤
        blockTimestamp := by
    simpa [latestRoundSlot, roundStartedAtSlot] using hPrevStarted
  have hPrevStartedVal : (s.storageMapUint 8 (s.storage 5)).val ≤ blockTimestamp.val := by
    simpa [lastStartedAtOf, roundStartedAtOf, latestRoundOf, latestRoundSlot, roundStartedAtSlot] using
      hPrevStarted
  have hPrevStartedValProp :
      (s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot)).val ≤
        blockTimestamp.val := by
    simpa [latestRoundSlot, roundStartedAtSlot] using hPrevStartedVal
  have hDataTsLeVal : dataTimestamp.val ≤ blockTimestamp.val := by
    simpa using hDataTsLe
  have hTimestampUnderflowProp :
      s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot) ≤
        blockTimestamp := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hTimeOrder
  have hTimestampUnderflowVal : (s.storageMapUint 9 (s.storage 5)).val ≤ blockTimestamp.val := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hTimeOrder
  have hTimestampUnderflowValProp :
      (s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot)).val ≤
        blockTimestamp.val := by
    simpa [latestRoundSlot, roundUpdatedAtSlot] using hTimestampUnderflowVal
  have hTimeGapProp :
      sub blockTimestamp
          (s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
            (s.storage CustomFeedGrowthSafe.latestRound.slot)) >
        3600 := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hTimeGap
  have hTimeGapVal : Core.Uint256.val 3600 < (sub blockTimestamp (s.storageMapUint 9 (s.storage 5))).val := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hTimeGap
  have hTimeGapValProp :
      Core.Uint256.val 3600 <
        (sub blockTimestamp
          (s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
            (s.storage CustomFeedGrowthSafe.latestRound.slot))).val := by
    simpa [latestRoundSlot, roundUpdatedAtSlot] using hTimeGapVal
  have hStartedProp :
      dataTimestamp >
        s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot) := by
    simpa [lastStartedAtOf, roundStartedAtOf, latestRoundOf, latestRoundSlot, roundStartedAtSlot] using
      hStarted
  have hStartedVal : (s.storageMapUint 8 (s.storage 5)).val < dataTimestamp.val := by
    simpa [lastStartedAtOf, roundStartedAtOf, latestRoundOf, latestRoundSlot, roundStartedAtSlot] using
      hStarted
  have hStartedValProp :
      (s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot)).val <
        dataTimestamp.val := by
    simpa [latestRoundSlot, roundStartedAtSlot] using hStartedVal
  by_cases hNeg : slt (signedDeviationOfSafeCall data dataTimestamp growthApr blockTimestamp s) 0 = true
  · have hNegRaw :
        slt
            (signedDeviationRaw (lastAnswerOf s blockTimestamp)
              (add data (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr) GROWTH_DENOMINATOR)))
            0 =
          true := by
      simpa [signedDeviationOfSafeCall, candidateLivePrice, applyGrowthNowRaw, applyGrowthAtRaw] using hNeg
    have hNegBranch :
        slt
            (sdiv
              (mul
                (mul
                  (sub
                    (add data
                      (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr)
                        315360000000000000))
                    (add (s.storageMapUint 7 (s.storage 5))
                      (sdiv
                        (mul
                          (mul (s.storageMapUint 7 (s.storage 5))
                            (sub blockTimestamp (s.storageMapUint 8 (s.storage 5))))
                          (s.storageMapUint 10 (s.storage 5)))
                        315360000000000000)))
                  100000000)
                100)
              (add (s.storageMapUint 7 (s.storage 5))
                (sdiv
                  (mul
                    (mul (s.storageMapUint 7 (s.storage 5))
                      (sub blockTimestamp (s.storageMapUint 8 (s.storage 5))))
                    (s.storageMapUint 10 (s.storage 5)))
                  315360000000000000)))
            0 =
          true := by
      simpa [signedDeviationOfSafeCall, signedDeviationRaw, candidateLivePrice, applyGrowthNowRaw,
        applyGrowthAtRaw, lastAnswerOf, lastRawAnswerOf, lastStartedAtOf, lastGrowthAprOf,
        roundAnswerOf, roundStartedAtOf, roundGrowthAprOf, latestRoundOf, latestRoundSlot,
        roundAnswerSlot, roundStartedAtSlot, roundGrowthAprSlot, GROWTH_DENOMINATOR,
        HUNDRED_ONE, ONE, YEAR_SECONDS] using hNeg
    have hNegCapProp :
        sub 0 (signedDeviationOfSafeCall data dataTimestamp growthApr blockTimestamp s) ≤
          s.storage CustomFeedGrowthSafe.maxAnswerDeviation.slot := by
      simpa [signedDeviationOfSafeCall, deviationOfSafeCall, candidateLivePrice, applyGrowthNowRaw,
        applyGrowthAtRaw, deviationAbsRaw, absSignedWord, maxAnswerDeviationOf, maxAnswerDeviationSlot,
        hCandidateNZDenom, hNegRaw] using hDeviationCap
    have hNegCapVal :
        (sub 0
              (sdiv
                (mul
                  (mul
                    (sub
                      (add data
                        (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr)
                          315360000000000000))
                      (add (s.storageMapUint 7 (s.storage 5))
                        (sdiv
                          (mul
                            (mul (s.storageMapUint 7 (s.storage 5))
                              (sub blockTimestamp (s.storageMapUint 8 (s.storage 5))))
                            (s.storageMapUint 10 (s.storage 5)))
                          315360000000000000)))
                    100000000)
                  100)
                (add (s.storageMapUint 7 (s.storage 5))
                  (sdiv
                    (mul
                      (mul (s.storageMapUint 7 (s.storage 5))
                        (sub blockTimestamp (s.storageMapUint 8 (s.storage 5))))
                      (s.storageMapUint 10 (s.storage 5)))
                    315360000000000000)))).val ≤
          (s.storage CustomFeedGrowthSafe.maxAnswerDeviation.slot).val := by
      simpa [signedDeviationOfSafeCall, signedDeviationRaw, candidateLivePrice, applyGrowthNowRaw,
        applyGrowthAtRaw, lastAnswerOf, lastRawAnswerOf, lastStartedAtOf, lastGrowthAprOf,
        roundAnswerOf, roundStartedAtOf, roundGrowthAprOf, latestRoundOf, latestRoundSlot,
        roundAnswerSlot, roundStartedAtSlot, roundGrowthAprSlot, GROWTH_DENOMINATOR,
        HUNDRED_ONE, ONE, YEAR_SECONDS] using hNegCapProp
    have hSafeRun :
        (CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s =
          (CustomFeedGrowthSafe.setRoundData data dataTimestamp growthApr blockTimestamp).run s := by
      have hOnlyUpEval :
          (getStorage CustomFeedGrowthSafe.onlyUp).run s =
            ContractResult.success (onlyUpWordOf s) s := by
        simp [onlyUpWordOf, onlyUpSlot, getStorage, Contract.run]
      have hLastUpdatedEval :
          (CustomFeedGrowthSafe.lastTimestamp.run s) =
            ContractResult.success (lastTimestampOf s) s := by
        exact lastTimestamp_eval s
      have hLastAnswerEval :
          ((CustomFeedGrowthSafe.lastAnswer blockTimestamp).run s) =
            ContractResult.success (lastAnswerOf s blockTimestamp) s := by
        exact lastAnswer_eval blockTimestamp s hPrevStarted
      have hCandidateEval :
          ((CustomFeedGrowthSafe.applyGrowth data growthApr dataTimestamp blockTimestamp).run s) =
            ContractResult.success (candidateLivePrice data dataTimestamp growthApr blockTimestamp) s := by
        simpa [candidateLivePrice, applyGrowthNowRaw] using
          (applyGrowth_eval data growthApr dataTimestamp blockTimestamp s hDataTsLe)
      have hDeviationEvalBase :
          ((CustomFeedGrowthSafe._getDeviation (lastAnswerOf s blockTimestamp)
                (candidateLivePrice data dataTimestamp growthApr blockTimestamp) false).run s) =
            ContractResult.success
              (sub 0
                (signedDeviationRaw (lastAnswerOf s blockTimestamp)
                  (candidateLivePrice data dataTimestamp growthApr blockTimestamp))) s := by
        apply getDeviation_eval_false_neg
        · simpa [candidateLivePrice, applyGrowthNowRaw, applyGrowthAtRaw] using hCandidateZero
        · simpa using hLastAnswerNZ
        · simpa [candidateLivePrice, applyGrowthNowRaw, applyGrowthAtRaw] using hNegRaw
      have hDeviationEval :
          ((CustomFeedGrowthSafe._getDeviation (lastAnswerOf s blockTimestamp)
                (candidateLivePrice data dataTimestamp growthApr blockTimestamp)
                (onlyUpWordOf s != 0)).run s) =
            ContractResult.success
              (sub 0
                (signedDeviationRaw (lastAnswerOf s blockTimestamp)
                  (candidateLivePrice data dataTimestamp growthApr blockTimestamp))) s := by
        simpa [onlyUpWordOf, onlyUpSlot, hOnlyUp0Num] using hDeviationEvalBase
      have hMaxDeviationEval :
          (getStorage CustomFeedGrowthSafe.maxAnswerDeviation).run s =
            ContractResult.success (maxAnswerDeviationOf s) s := by
        simp [maxAnswerDeviationOf, maxAnswerDeviationSlot, getStorage, Contract.run]
      have hLastStartedEval :
          (CustomFeedGrowthSafe.lastStartedAt.run s) =
            ContractResult.success (lastStartedAtOf s) s := by
        exact lastStartedAt_eval s
      have hLastUpdatedNZBranch :
          ((lastTimestampOf s != 0) = true) := by
        simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
          hLastUpdatedBranch
      unfold CustomFeedGrowthSafe.setRoundDataSafe Verity.require
      simp only [Bind.bind]
      rw [bind_run_success_same_state _ _ _ _ hOnlyUpEval]
      rw [bind_run_success_same_state _ _ _ _ hLastUpdatedEval]
      rw [if_pos hLastUpdatedNZBranch]
      rw [bind_run_success_same_state _ _ _ _ hLastAnswerEval]
      rw [bind_run_success_same_state _ _ _ _ hCandidateEval]
      rw [bind_run_success_same_state _ _ _ _ hDeviationEval]
      rw [bind_run_success_same_state _ _ _ _ hMaxDeviationEval]
      have hNegCapBranch :
          decide
              (sub 0
                  (signedDeviationRaw (lastAnswerOf s blockTimestamp)
                    (candidateLivePrice data dataTimestamp growthApr blockTimestamp)) ≤
                maxAnswerDeviationOf s) =
            true := by
        simpa [signedDeviationOfSafeCall, candidateLivePrice, applyGrowthNowRaw, applyGrowthAtRaw] using
          hNegCapProp
      have hOnlyUpOffBranch : ¬ ((onlyUpWordOf s != 0) = true) := by
        simpa [hOnlyUp0]
      have hTimeOrderBranch : decide (lastTimestampOf s ≤ blockTimestamp) = true := by
        simpa using hTimeOrder
      have hTimeGapBranch : decide (sub blockTimestamp (lastTimestampOf s) > 3600) = true := by
        simpa using hTimeGap
      have hStartedBranch : decide (dataTimestamp > lastStartedAtOf s) = true := by
        simpa using hStarted
      rw [hNegCapBranch]
      rw [if_neg hOnlyUpOffBranch]
      rw [hTimeOrderBranch]
      rw [hTimeGapBranch]
      simp [Verity.require, Verity.pure, Pure.pure, Contract.run, getStorage, getMappingUint, setStorage,
        setMappingUint, Verity.bind, Bind.bind, CustomFeedGrowthSafe.lastStartedAt,
        hStartedBranch, lastStartedAtOf, latestRoundOf, latestRoundSlot, roundStartedAtOf, roundStartedAtSlot]
      have hStartedCheckEval :
          (if
              (s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
                    (s.storage CustomFeedGrowthSafe.latestRound.slot)).val <
                dataTimestamp.val then
              ContractResult.success () s
            else
              ContractResult.revert "CAG: timestamp <= last startedAt" s) =
            ContractResult.success () s := by
        simp [hStartedValProp]
      have hStartedCheckEvalNum :
          (if (s.storageMapUint 8 (s.storage 5)).val < dataTimestamp.val then
              ContractResult.success () s
            else
              ContractResult.revert "CAG: timestamp <= last startedAt" s) =
            ContractResult.success () s := by
        simpa [latestRoundSlot, roundStartedAtSlot] using hStartedCheckEval
      simp [CustomFeedGrowthSafe.setRoundData, Verity.require, Verity.pure, Pure.pure, Contract.run, getStorage,
        getMappingUint, setStorage, setMappingUint, Verity.bind, Bind.bind, hStartedCheckEvalNum,
        hDataLoBranch, hDataHiBranch, hGrowthLoBranch, hGrowthHiBranch, hDataTsLt]
    have hSafeEq :
        ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd =
          ((CustomFeedGrowthSafe.setRoundData data dataTimestamp growthApr blockTimestamp).run s).snd := by
      simpa using congrArg ContractResult.snd hSafeRun
    constructor
    · rw [hSafeEq]
      simpa using
        (setRoundData_writes data dataTimestamp growthApr blockTimestamp s
          hDataLoBranch hDataHiBranch hGrowthLoBranch hGrowthHiBranch hDataTsLt storageSlot mapSlot k).1
    · rw [hSafeEq]
      simpa using
        (setRoundData_writes data dataTimestamp growthApr blockTimestamp s
          hDataLoBranch hDataHiBranch hGrowthLoBranch hGrowthHiBranch hDataTsLt storageSlot mapSlot k).2
  · have hNegRaw :
        slt
            (signedDeviationRaw (lastAnswerOf s blockTimestamp)
              (add data (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr) GROWTH_DENOMINATOR)))
            0 =
          false := by
      simpa [signedDeviationOfSafeCall, candidateLivePrice, applyGrowthNowRaw, applyGrowthAtRaw] using hNeg
    have hNegBranch :
        slt
            (sdiv
              (mul
                (mul
                  (sub
                    (add data
                      (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr)
                        315360000000000000))
                    (add (s.storageMapUint 7 (s.storage 5))
                      (sdiv
                        (mul
                          (mul (s.storageMapUint 7 (s.storage 5))
                            (sub blockTimestamp (s.storageMapUint 8 (s.storage 5))))
                          (s.storageMapUint 10 (s.storage 5)))
                        315360000000000000)))
                  100000000)
                100)
              (add (s.storageMapUint 7 (s.storage 5))
                (sdiv
                  (mul
                    (mul (s.storageMapUint 7 (s.storage 5))
                      (sub blockTimestamp (s.storageMapUint 8 (s.storage 5))))
                    (s.storageMapUint 10 (s.storage 5)))
                  315360000000000000)))
            0 =
          false := by
      simpa [signedDeviationOfSafeCall, signedDeviationRaw, candidateLivePrice, applyGrowthNowRaw,
        applyGrowthAtRaw, lastAnswerOf, lastRawAnswerOf, lastStartedAtOf, lastGrowthAprOf,
        roundAnswerOf, roundStartedAtOf, roundGrowthAprOf, latestRoundOf, latestRoundSlot,
        roundAnswerSlot, roundStartedAtSlot, roundGrowthAprSlot, GROWTH_DENOMINATOR,
        HUNDRED_ONE, ONE, YEAR_SECONDS] using hNeg
    have hPosCapProp :
        signedDeviationOfSafeCall data dataTimestamp growthApr blockTimestamp s ≤
          s.storage CustomFeedGrowthSafe.maxAnswerDeviation.slot := by
      simpa [signedDeviationOfSafeCall, deviationOfSafeCall, candidateLivePrice, applyGrowthNowRaw,
        applyGrowthAtRaw, deviationAbsRaw, absSignedWord, maxAnswerDeviationOf, maxAnswerDeviationSlot,
        hCandidateNZDenom, hNegRaw] using hDeviationCap
    have hPosCapVal :
        (sdiv
              (mul
                (mul
                  (sub
                    (add data
                      (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr)
                        315360000000000000))
                    (add (s.storageMapUint 7 (s.storage 5))
                      (sdiv
                        (mul
                          (mul (s.storageMapUint 7 (s.storage 5))
                            (sub blockTimestamp (s.storageMapUint 8 (s.storage 5))))
                          (s.storageMapUint 10 (s.storage 5)))
                        315360000000000000)))
                  100000000)
                100)
              (add (s.storageMapUint 7 (s.storage 5))
                (sdiv
                  (mul
                    (mul (s.storageMapUint 7 (s.storage 5))
                      (sub blockTimestamp (s.storageMapUint 8 (s.storage 5))))
                    (s.storageMapUint 10 (s.storage 5)))
                  315360000000000000))).val ≤
          (s.storage CustomFeedGrowthSafe.maxAnswerDeviation.slot).val := by
      simpa [signedDeviationOfSafeCall, signedDeviationRaw, candidateLivePrice, applyGrowthNowRaw,
        applyGrowthAtRaw, lastAnswerOf, lastRawAnswerOf, lastStartedAtOf, lastGrowthAprOf,
        roundAnswerOf, roundStartedAtOf, roundGrowthAprOf, latestRoundOf, latestRoundSlot,
        roundAnswerSlot, roundStartedAtSlot, roundGrowthAprSlot, GROWTH_DENOMINATOR,
        HUNDRED_ONE, ONE, YEAR_SECONDS] using hPosCapProp
    have hSafeRun :
        (CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s =
          (CustomFeedGrowthSafe.setRoundData data dataTimestamp growthApr blockTimestamp).run s := by
      have hOnlyUpEval :
          (getStorage CustomFeedGrowthSafe.onlyUp).run s =
            ContractResult.success (onlyUpWordOf s) s := by
        simp [onlyUpWordOf, onlyUpSlot, getStorage, Contract.run]
      have hLastUpdatedEval :
          (CustomFeedGrowthSafe.lastTimestamp.run s) =
            ContractResult.success (lastTimestampOf s) s := by
        exact lastTimestamp_eval s
      have hLastAnswerEval :
          ((CustomFeedGrowthSafe.lastAnswer blockTimestamp).run s) =
            ContractResult.success (lastAnswerOf s blockTimestamp) s := by
        exact lastAnswer_eval blockTimestamp s hPrevStarted
      have hCandidateEval :
          ((CustomFeedGrowthSafe.applyGrowth data growthApr dataTimestamp blockTimestamp).run s) =
            ContractResult.success (candidateLivePrice data dataTimestamp growthApr blockTimestamp) s := by
        simpa [candidateLivePrice, applyGrowthNowRaw] using
          (applyGrowth_eval data growthApr dataTimestamp blockTimestamp s hDataTsLe)
      have hDeviationEvalBase :
          ((CustomFeedGrowthSafe._getDeviation (lastAnswerOf s blockTimestamp)
                (candidateLivePrice data dataTimestamp growthApr blockTimestamp) false).run s) =
            ContractResult.success
              (signedDeviationRaw (lastAnswerOf s blockTimestamp)
                (candidateLivePrice data dataTimestamp growthApr blockTimestamp)) s := by
        apply getDeviation_eval_false_nonneg
        · simpa [candidateLivePrice, applyGrowthNowRaw, applyGrowthAtRaw] using hCandidateZero
        · simpa using hLastAnswerNZ
        · simpa [candidateLivePrice, applyGrowthNowRaw, applyGrowthAtRaw] using hNegRaw
      have hDeviationEval :
          ((CustomFeedGrowthSafe._getDeviation (lastAnswerOf s blockTimestamp)
                (candidateLivePrice data dataTimestamp growthApr blockTimestamp)
                (onlyUpWordOf s != 0)).run s) =
            ContractResult.success
              (signedDeviationRaw (lastAnswerOf s blockTimestamp)
                (candidateLivePrice data dataTimestamp growthApr blockTimestamp)) s := by
        simpa only [onlyUpWordOf, onlyUpSlot, hOnlyUp0Num] using hDeviationEvalBase
      have hMaxDeviationEval :
          (getStorage CustomFeedGrowthSafe.maxAnswerDeviation).run s =
            ContractResult.success (maxAnswerDeviationOf s) s := by
        simp [maxAnswerDeviationOf, maxAnswerDeviationSlot, getStorage, Contract.run]
      have hLastStartedEval :
          (CustomFeedGrowthSafe.lastStartedAt.run s) =
            ContractResult.success (lastStartedAtOf s) s := by
        exact lastStartedAt_eval s
      have hLastUpdatedNZBranch :
          ((lastTimestampOf s != 0) = true) := by
        simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
          hLastUpdatedBranch
      unfold CustomFeedGrowthSafe.setRoundDataSafe Verity.require
      simp only [Bind.bind]
      rw [bind_run_success_same_state _ _ _ _ hOnlyUpEval]
      rw [bind_run_success_same_state _ _ _ _ hLastUpdatedEval]
      rw [if_pos hLastUpdatedNZBranch]
      rw [bind_run_success_same_state _ _ _ _ hLastAnswerEval]
      rw [bind_run_success_same_state _ _ _ _ hCandidateEval]
      rw [bind_run_success_same_state _ _ _ _ hDeviationEval]
      rw [bind_run_success_same_state _ _ _ _ hMaxDeviationEval]
      have hPosCapBranch :
          decide
              (signedDeviationRaw (lastAnswerOf s blockTimestamp)
                  (candidateLivePrice data dataTimestamp growthApr blockTimestamp) ≤
                maxAnswerDeviationOf s) =
            true := by
        simpa [signedDeviationOfSafeCall, candidateLivePrice, applyGrowthNowRaw, applyGrowthAtRaw] using
          hPosCapProp
      have hOnlyUpOffBranch : ¬ ((onlyUpWordOf s != 0) = true) := by
        simpa [hOnlyUp0]
      have hTimeOrderBranch : decide (lastTimestampOf s ≤ blockTimestamp) = true := by
        simpa using hTimeOrder
      have hTimeGapBranch : decide (sub blockTimestamp (lastTimestampOf s) > 3600) = true := by
        simpa using hTimeGap
      have hStartedBranch : decide (dataTimestamp > lastStartedAtOf s) = true := by
        simpa using hStarted
      rw [hPosCapBranch]
      rw [if_neg hOnlyUpOffBranch]
      rw [hTimeOrderBranch]
      rw [hTimeGapBranch]
      simp [Verity.require, Verity.pure, Pure.pure, Contract.run, getStorage, getMappingUint, setStorage,
        setMappingUint, Verity.bind, Bind.bind, CustomFeedGrowthSafe.lastStartedAt,
        hStartedBranch, lastStartedAtOf, latestRoundOf, latestRoundSlot, roundStartedAtOf, roundStartedAtSlot]
      have hStartedCheckEval :
          (if
              (s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
                    (s.storage CustomFeedGrowthSafe.latestRound.slot)).val <
                dataTimestamp.val then
              ContractResult.success () s
            else
              ContractResult.revert "CAG: timestamp <= last startedAt" s) =
            ContractResult.success () s := by
        simp [hStartedValProp]
      have hStartedCheckEvalNum :
          (if (s.storageMapUint 8 (s.storage 5)).val < dataTimestamp.val then
              ContractResult.success () s
            else
              ContractResult.revert "CAG: timestamp <= last startedAt" s) =
            ContractResult.success () s := by
        simpa [latestRoundSlot, roundStartedAtSlot] using hStartedCheckEval
      simp [CustomFeedGrowthSafe.setRoundData, Verity.require, Verity.pure, Pure.pure, Contract.run, getStorage,
        getMappingUint, setStorage, setMappingUint, Verity.bind, Bind.bind, hStartedCheckEvalNum,
        hDataLoBranch, hDataHiBranch, hGrowthLoBranch, hGrowthHiBranch, hDataTsLt]
    have hSafeEq :
        ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd =
          ((CustomFeedGrowthSafe.setRoundData data dataTimestamp growthApr blockTimestamp).run s).snd := by
      simpa using congrArg ContractResult.snd hSafeRun
    constructor
    · rw [hSafeEq]
      simpa using
        (setRoundData_writes data dataTimestamp growthApr blockTimestamp s
          hDataLoBranch hDataHiBranch hGrowthLoBranch hGrowthHiBranch hDataTsLt storageSlot mapSlot k).1
    · rw [hSafeEq]
      simpa using
        (setRoundData_writes data dataTimestamp growthApr blockTimestamp s
          hDataLoBranch hDataHiBranch hGrowthLoBranch hGrowthHiBranch hDataTsLt storageSlot mapSlot k).2

private theorem setRoundDataSafe_candidate_nonzero_onlyup_on_writes
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hLastUpdated0 : ¬ lastTimestampOf s = 0)
    (hPrevStarted : lastStartedAtOf s <= blockTimestamp)
    (hDataTsLe : dataTimestamp <= blockTimestamp)
    (hLastAnswerNZ : lastAnswerOf s blockTimestamp != 0)
    (hOnlyUpDeviation :
      slt (signedDeviationOfSafeCall data dataTimestamp growthApr blockTimestamp s) 0 = false)
    (hDeviationCap :
      deviationOfSafeCall data dataTimestamp growthApr blockTimestamp s <= maxAnswerDeviationOf s)
    (hCandidateZero : ¬ candidateLivePrice data dataTimestamp growthApr blockTimestamp = 0)
    (hOnlyUp0 : ¬ onlyUpWordOf s = 0)
    (hOnlyUpApr : slt growthApr 0 = false)
    (hTimeOrder : lastTimestampOf s <= blockTimestamp)
    (hTimeGap : sub blockTimestamp (lastTimestampOf s) > 3600)
    (hStarted : dataTimestamp > lastStartedAtOf s)
    (hDataLo : slt data (minAnswerOf s) = false)
    (hDataHi : sgt data (maxAnswerOf s) = false)
    (hGrowthLo : slt growthApr (minGrowthAprOf s) = false)
    (hGrowthHi : sgt growthApr (maxGrowthAprOf s) = false)
    (hDataTsLt : dataTimestamp < blockTimestamp)
    (storageSlot mapSlot : Nat) (k : Uint256) :
    let s' := ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd
    s'.storage storageSlot = writeStorageAfterRound s storageSlot ∧
      s'.storageMapUint mapSlot k = writeMapUintAfterRound data dataTimestamp growthApr blockTimestamp s mapSlot k := by
  have hLastUpdatedNZNum : s.storageMapUint 9 (s.storage 5) ≠ 0 := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hLastUpdated0
  have hOnlyUp0Num : s.storage 6 ≠ 0 := by simpa [onlyUpWordOf, onlyUpSlot] using hOnlyUp0
  have hDataLoNum : slt data (s.storage 1) = false := by simpa [minAnswerOf, minAnswerSlot] using hDataLo
  have hDataHiNum : sgt data (s.storage 2) = false := by simpa [maxAnswerOf, maxAnswerSlot] using hDataHi
  have hGrowthLoNum : slt growthApr (s.storage 3) = false := by
    simpa [minGrowthAprOf, minGrowthAprSlot] using hGrowthLo
  have hGrowthHiNum : sgt growthApr (s.storage 4) = false := by
    simpa [maxGrowthAprOf, maxGrowthAprSlot] using hGrowthHi
  have hCandidateNZNum :
      add data (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr) 315360000000000000) ≠ 0 := by
    simpa [candidateLivePrice, applyGrowthNowRaw, applyGrowthAtRaw] using hCandidateZero
  have hCandidateNZDenom :
      add data (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr) GROWTH_DENOMINATOR) ≠ 0 := by
    simpa [GROWTH_DENOMINATOR, HUNDRED_ONE, ONE, YEAR_SECONDS] using hCandidateNZNum
  have hLastAnswerNZNum :
      add (s.storageMapUint 7 (s.storage 5))
          (sdiv
            (mul
              (mul (s.storageMapUint 7 (s.storage 5))
                (sub blockTimestamp (s.storageMapUint 8 (s.storage 5))))
              (s.storageMapUint 10 (s.storage 5)))
            315360000000000000) ≠ 0 := by
    simpa [lastAnswerOf, applyGrowthNowRaw, applyGrowthAtRaw,
      lastRawAnswerOf, lastStartedAtOf, lastGrowthAprOf,
      roundAnswerOf, roundStartedAtOf, roundGrowthAprOf, latestRoundOf,
      latestRoundSlot, roundAnswerSlot, roundStartedAtSlot, roundGrowthAprSlot] using hLastAnswerNZ
  have hLastUpdatedBranch :
      ((s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
            (s.storage CustomFeedGrowthSafe.latestRound.slot) != 0) =
          true) := by
    simpa [latestRoundSlot, roundUpdatedAtSlot, hLastUpdatedNZNum]
  have hCandidateZeroBranch :
      ¬ ((add data
              (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr) 315360000000000000) ==
            0) =
          true) := by
    simp [hCandidateNZNum]
  have hLastAnswerNZBranch :
      ((add
              (s.storageMapUint CustomFeedGrowthSafe.roundAnswer.slot
                (s.storage CustomFeedGrowthSafe.latestRound.slot))
              (sdiv
                (mul
                  (mul
                    (s.storageMapUint CustomFeedGrowthSafe.roundAnswer.slot
                      (s.storage CustomFeedGrowthSafe.latestRound.slot))
                    (sub blockTimestamp
                      (s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
                        (s.storage CustomFeedGrowthSafe.latestRound.slot))))
                  (s.storageMapUint CustomFeedGrowthSafe.roundGrowthApr.slot
                    (s.storage CustomFeedGrowthSafe.latestRound.slot)))
                315360000000000000) !=
            0) =
        true) := by
    simpa [latestRoundSlot, roundAnswerSlot, roundStartedAtSlot, roundGrowthAprSlot, hLastAnswerNZNum]
  have hOnlyUpBranch : ((s.storage CustomFeedGrowthSafe.onlyUp.slot != 0) = true) := by
    simpa [onlyUpSlot, hOnlyUp0Num]
  have hOnlyUpAprBranch : ¬ (slt growthApr 0 = true) := by simpa [hOnlyUpApr]
  have hDataLoBranch : ¬ (slt data (s.storage CustomFeedGrowthSafe.minAnswer.slot) = true) := by
    simpa [minAnswerSlot, hDataLoNum]
  have hDataHiBranch : ¬ (sgt data (s.storage CustomFeedGrowthSafe.maxAnswer.slot) = true) := by
    simpa [maxAnswerSlot, hDataHiNum]
  have hGrowthLoBranch :
      ¬ (slt growthApr (s.storage CustomFeedGrowthSafe.minGrowthApr.slot) = true) := by
    simpa [minGrowthAprSlot, hGrowthLoNum]
  have hGrowthHiBranch :
      ¬ (sgt growthApr (s.storage CustomFeedGrowthSafe.maxGrowthApr.slot) = true) := by
    simpa [maxGrowthAprSlot, hGrowthHiNum]
  have hPrevStartedProp :
      s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot) ≤
        blockTimestamp := by
    simpa [latestRoundSlot, roundStartedAtSlot] using hPrevStarted
  have hPrevStartedVal : (s.storageMapUint 8 (s.storage 5)).val ≤ blockTimestamp.val := by
    simpa [lastStartedAtOf, roundStartedAtOf, latestRoundOf, latestRoundSlot, roundStartedAtSlot] using
      hPrevStarted
  have hPrevStartedValProp :
      (s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot)).val ≤
        blockTimestamp.val := by
    simpa [latestRoundSlot, roundStartedAtSlot] using hPrevStartedVal
  have hDataTsLeVal : dataTimestamp.val ≤ blockTimestamp.val := by
    simpa using hDataTsLe
  have hTimestampUnderflowProp :
      s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot) ≤
        blockTimestamp := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hTimeOrder
  have hTimestampUnderflowVal : (s.storageMapUint 9 (s.storage 5)).val ≤ blockTimestamp.val := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hTimeOrder
  have hTimestampUnderflowValProp :
      (s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot)).val ≤
        blockTimestamp.val := by
    simpa [latestRoundSlot, roundUpdatedAtSlot] using hTimestampUnderflowVal
  have hTimeGapProp :
      sub blockTimestamp
          (s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
            (s.storage CustomFeedGrowthSafe.latestRound.slot)) >
        3600 := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hTimeGap
  have hTimeGapVal : Core.Uint256.val 3600 < (sub blockTimestamp (s.storageMapUint 9 (s.storage 5))).val := by
    simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
      hTimeGap
  have hTimeGapValProp :
      Core.Uint256.val 3600 <
        (sub blockTimestamp
          (s.storageMapUint CustomFeedGrowthSafe.roundUpdatedAt.slot
            (s.storage CustomFeedGrowthSafe.latestRound.slot))).val := by
    simpa [latestRoundSlot, roundUpdatedAtSlot] using hTimeGapVal
  have hStartedProp :
      dataTimestamp >
        s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot) := by
    simpa [lastStartedAtOf, roundStartedAtOf, latestRoundOf, latestRoundSlot, roundStartedAtSlot] using
      hStarted
  have hStartedVal : (s.storageMapUint 8 (s.storage 5)).val < dataTimestamp.val := by
    simpa [lastStartedAtOf, roundStartedAtOf, latestRoundOf, latestRoundSlot, roundStartedAtSlot] using
      hStarted
  have hStartedValProp :
      (s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
          (s.storage CustomFeedGrowthSafe.latestRound.slot)).val <
        dataTimestamp.val := by
    simpa [latestRoundSlot, roundStartedAtSlot] using hStartedVal
  have hOnlyUpDeviationRaw :
      slt
          (signedDeviationRaw (lastAnswerOf s blockTimestamp)
            (add data (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr) GROWTH_DENOMINATOR)))
          0 =
        false := by
    simpa [signedDeviationOfSafeCall, candidateLivePrice, applyGrowthNowRaw, applyGrowthAtRaw] using
      hOnlyUpDeviation
  have hOnlyUpDeviationBranch :
      slt
          (sdiv
            (mul
              (mul
                (sub
                  (add data
                    (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr)
                      315360000000000000))
                  (add (s.storageMapUint 7 (s.storage 5))
                    (sdiv
                      (mul
                        (mul (s.storageMapUint 7 (s.storage 5))
                          (sub blockTimestamp (s.storageMapUint 8 (s.storage 5))))
                        (s.storageMapUint 10 (s.storage 5)))
                      315360000000000000)))
                100000000)
              100)
            (add (s.storageMapUint 7 (s.storage 5))
              (sdiv
                (mul
                  (mul (s.storageMapUint 7 (s.storage 5))
                    (sub blockTimestamp (s.storageMapUint 8 (s.storage 5))))
                  (s.storageMapUint 10 (s.storage 5)))
                315360000000000000)))
          0 =
        false := by
    simpa [signedDeviationOfSafeCall, signedDeviationRaw, candidateLivePrice, applyGrowthNowRaw,
      applyGrowthAtRaw, lastAnswerOf, lastRawAnswerOf, lastStartedAtOf, lastGrowthAprOf,
      roundAnswerOf, roundStartedAtOf, roundGrowthAprOf, latestRoundOf, latestRoundSlot,
      roundAnswerSlot, roundStartedAtSlot, roundGrowthAprSlot, GROWTH_DENOMINATOR,
      HUNDRED_ONE, ONE, YEAR_SECONDS] using hOnlyUpDeviation
  have hPosCapProp :
      signedDeviationOfSafeCall data dataTimestamp growthApr blockTimestamp s ≤
        s.storage CustomFeedGrowthSafe.maxAnswerDeviation.slot := by
    simpa [signedDeviationOfSafeCall, deviationOfSafeCall, candidateLivePrice, applyGrowthNowRaw,
      applyGrowthAtRaw, deviationAbsRaw, absSignedWord, maxAnswerDeviationOf, maxAnswerDeviationSlot,
      hCandidateNZDenom, hOnlyUpDeviationRaw] using hDeviationCap
  have hPosCapVal :
      (sdiv
            (mul
              (mul
                (sub
                  (add data
                    (sdiv (mul (mul data (sub blockTimestamp dataTimestamp)) growthApr)
                      315360000000000000))
                  (add (s.storageMapUint 7 (s.storage 5))
                    (sdiv
                      (mul
                        (mul (s.storageMapUint 7 (s.storage 5))
                          (sub blockTimestamp (s.storageMapUint 8 (s.storage 5))))
                        (s.storageMapUint 10 (s.storage 5)))
                      315360000000000000)))
                100000000)
              100)
            (add (s.storageMapUint 7 (s.storage 5))
              (sdiv
                (mul
                  (mul (s.storageMapUint 7 (s.storage 5))
                    (sub blockTimestamp (s.storageMapUint 8 (s.storage 5))))
                  (s.storageMapUint 10 (s.storage 5)))
                315360000000000000))).val ≤
        (s.storage CustomFeedGrowthSafe.maxAnswerDeviation.slot).val := by
    simpa [signedDeviationOfSafeCall, signedDeviationRaw, candidateLivePrice, applyGrowthNowRaw,
      applyGrowthAtRaw, lastAnswerOf, lastRawAnswerOf, lastStartedAtOf, lastGrowthAprOf,
      roundAnswerOf, roundStartedAtOf, roundGrowthAprOf, latestRoundOf, latestRoundSlot,
      roundAnswerSlot, roundStartedAtSlot, roundGrowthAprSlot, GROWTH_DENOMINATOR,
      HUNDRED_ONE, ONE, YEAR_SECONDS] using hPosCapProp
  have hSafeRun :
      (CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s =
        (CustomFeedGrowthSafe.setRoundData data dataTimestamp growthApr blockTimestamp).run s := by
    have hOnlyUpEval :
        (getStorage CustomFeedGrowthSafe.onlyUp).run s =
          ContractResult.success (onlyUpWordOf s) s := by
      simp [onlyUpWordOf, onlyUpSlot, getStorage, Contract.run]
    have hLastUpdatedEval :
        (CustomFeedGrowthSafe.lastTimestamp.run s) =
          ContractResult.success (lastTimestampOf s) s := by
      exact lastTimestamp_eval s
    have hLastAnswerEval :
        ((CustomFeedGrowthSafe.lastAnswer blockTimestamp).run s) =
          ContractResult.success (lastAnswerOf s blockTimestamp) s := by
      exact lastAnswer_eval blockTimestamp s hPrevStarted
    have hCandidateEval :
        ((CustomFeedGrowthSafe.applyGrowth data growthApr dataTimestamp blockTimestamp).run s) =
          ContractResult.success (candidateLivePrice data dataTimestamp growthApr blockTimestamp) s := by
      simpa [candidateLivePrice, applyGrowthNowRaw] using
        (applyGrowth_eval data growthApr dataTimestamp blockTimestamp s hDataTsLe)
    have hDeviationEvalBase :
        ((CustomFeedGrowthSafe._getDeviation (lastAnswerOf s blockTimestamp)
              (candidateLivePrice data dataTimestamp growthApr blockTimestamp) true).run s) =
          ContractResult.success
            (signedDeviationRaw (lastAnswerOf s blockTimestamp)
              (candidateLivePrice data dataTimestamp growthApr blockTimestamp)) s := by
      apply getDeviation_eval_true_nonneg
      · simpa [candidateLivePrice, applyGrowthNowRaw, applyGrowthAtRaw] using hCandidateZero
      · simpa using hLastAnswerNZ
      · simpa [candidateLivePrice, applyGrowthNowRaw, applyGrowthAtRaw] using hOnlyUpDeviationRaw
    have hDeviationEval :
        ((CustomFeedGrowthSafe._getDeviation (lastAnswerOf s blockTimestamp)
              (candidateLivePrice data dataTimestamp growthApr blockTimestamp)
              (onlyUpWordOf s != 0)).run s) =
          ContractResult.success
            (signedDeviationRaw (lastAnswerOf s blockTimestamp)
              (candidateLivePrice data dataTimestamp growthApr blockTimestamp)) s := by
      simpa [onlyUpWordOf, onlyUpSlot, hOnlyUp0Num] using hDeviationEvalBase
    have hMaxDeviationEval :
        (getStorage CustomFeedGrowthSafe.maxAnswerDeviation).run s =
          ContractResult.success (maxAnswerDeviationOf s) s := by
      simp [maxAnswerDeviationOf, maxAnswerDeviationSlot, getStorage, Contract.run]
    have hLastUpdatedNZBranch :
        ((lastTimestampOf s != 0) = true) := by
      simpa [lastTimestampOf, roundUpdatedAtOf, latestRoundOf, latestRoundSlot, roundUpdatedAtSlot] using
        hLastUpdatedBranch
    unfold CustomFeedGrowthSafe.setRoundDataSafe Verity.require
    simp only [Bind.bind]
    rw [bind_run_success_same_state _ _ _ _ hOnlyUpEval]
    rw [bind_run_success_same_state _ _ _ _ hLastUpdatedEval]
    rw [if_pos hLastUpdatedNZBranch]
    rw [bind_run_success_same_state _ _ _ _ hLastAnswerEval]
    rw [bind_run_success_same_state _ _ _ _ hCandidateEval]
    rw [bind_run_success_same_state _ _ _ _ hDeviationEval]
    rw [bind_run_success_same_state _ _ _ _ hMaxDeviationEval]
    have hPosCapBranch :
        decide
            (signedDeviationRaw (lastAnswerOf s blockTimestamp)
                (candidateLivePrice data dataTimestamp growthApr blockTimestamp) ≤
              maxAnswerDeviationOf s) =
          true := by
      simpa [signedDeviationOfSafeCall, candidateLivePrice, applyGrowthNowRaw, applyGrowthAtRaw] using
        hPosCapProp
    have hOnlyUpOnBranch : ((onlyUpWordOf s != 0) = true) := by
      simp [hOnlyUp0]
    have hTimeOrderBranch : decide (lastTimestampOf s ≤ blockTimestamp) = true := by
      simpa using hTimeOrder
    have hTimeGapBranch : decide (sub blockTimestamp (lastTimestampOf s) > 3600) = true := by
      simpa using hTimeGap
    have hStartedBranch : decide (dataTimestamp > lastStartedAtOf s) = true := by
      simpa using hStarted
    rw [hPosCapBranch]
    rw [if_pos hOnlyUpOnBranch]
    rw [if_neg hOnlyUpAprBranch]
    rw [hTimeOrderBranch]
    rw [hTimeGapBranch]
    simp [Verity.require, Verity.pure, Pure.pure, Contract.run, getStorage, getMappingUint, setStorage,
      setMappingUint, Verity.bind, Bind.bind, CustomFeedGrowthSafe.lastStartedAt,
      hStartedBranch, lastStartedAtOf, latestRoundOf, latestRoundSlot, roundStartedAtOf, roundStartedAtSlot]
    have hStartedCheckEval :
        (if
            (s.storageMapUint CustomFeedGrowthSafe.roundStartedAt.slot
                  (s.storage CustomFeedGrowthSafe.latestRound.slot)).val <
              dataTimestamp.val then
            ContractResult.success () s
          else
            ContractResult.revert "CAG: timestamp <= last startedAt" s) =
          ContractResult.success () s := by
      simp [hStartedValProp]
    have hStartedCheckEvalNum :
        (if (s.storageMapUint 8 (s.storage 5)).val < dataTimestamp.val then
            ContractResult.success () s
          else
            ContractResult.revert "CAG: timestamp <= last startedAt" s) =
          ContractResult.success () s := by
      simpa [latestRoundSlot, roundStartedAtSlot] using hStartedCheckEval
    simp [CustomFeedGrowthSafe.setRoundData, Verity.require, Verity.pure, Pure.pure, Contract.run, getStorage,
      getMappingUint, setStorage, setMappingUint, Verity.bind, Bind.bind, hStartedCheckEvalNum,
      hDataLoBranch, hDataHiBranch, hGrowthLoBranch, hGrowthHiBranch, hDataTsLt]
  have hSafeEq :
      ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd =
        ((CustomFeedGrowthSafe.setRoundData data dataTimestamp growthApr blockTimestamp).run s).snd := by
    simpa using congrArg ContractResult.snd hSafeRun
  constructor
  · rw [hSafeEq]
    simpa using
      (setRoundData_writes data dataTimestamp growthApr blockTimestamp s
        hDataLoBranch hDataHiBranch hGrowthLoBranch hGrowthHiBranch hDataTsLt storageSlot mapSlot k).1
  · rw [hSafeEq]
    simpa using
      (setRoundData_writes data dataTimestamp growthApr blockTimestamp s
        hDataLoBranch hDataHiBranch hGrowthLoBranch hGrowthHiBranch hDataTsLt storageSlot mapSlot k).2

private theorem setRoundDataSafe_projected_writes
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hPrevStarted : lastTimestampOf s != 0 → lastStartedAtOf s <= blockTimestamp)
    (hDataTsLe : lastTimestampOf s != 0 → dataTimestamp <= blockTimestamp)
    (hLastAnswerNZ :
      lastTimestampOf s != 0 → candidateLivePrice data dataTimestamp growthApr blockTimestamp ≠ 0 →
        lastAnswerOf s blockTimestamp != 0)
    (hOnlyUpDeviation :
      lastTimestampOf s != 0 → onlyUpWordOf s != 0 →
        slt (signedDeviationOfSafeCall data dataTimestamp growthApr blockTimestamp s) 0 = false)
    (hDeviationCap :
      lastTimestampOf s != 0 →
        deviationOfSafeCall data dataTimestamp growthApr blockTimestamp s <= maxAnswerDeviationOf s)
    (hOnlyUpApr : onlyUpWordOf s != 0 → slt growthApr 0 = false)
    (hTimeOrder : lastTimestampOf s <= blockTimestamp)
    (hTimeGap : sub blockTimestamp (lastTimestampOf s) > 3600)
    (hStarted : dataTimestamp > lastStartedAtOf s)
    (hDataLo : slt data (minAnswerOf s) = false)
    (hDataHi : sgt data (maxAnswerOf s) = false)
    (hGrowthLo : slt growthApr (minGrowthAprOf s) = false)
    (hGrowthHi : sgt growthApr (maxGrowthAprOf s) = false)
    (hDataTsLt : dataTimestamp < blockTimestamp)
    (storageSlot mapSlot : Nat) (k : Uint256) :
    let s' := ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd
    s'.storage storageSlot = writeStorageAfterRound s storageSlot ∧
      s'.storageMapUint mapSlot k = writeMapUintAfterRound data dataTimestamp growthApr blockTimestamp s mapSlot k := by
  by_cases hLastUpdated0 : lastTimestampOf s = 0
  · by_cases hOnlyUp0 : onlyUpWordOf s = 0
    · exact setRoundDataSafe_zero_history_onlyup_off_writes data dataTimestamp growthApr blockTimestamp s
        hLastUpdated0 hOnlyUp0 hTimeOrder hTimeGap hStarted hDataLo hDataHi hGrowthLo hGrowthHi
        hDataTsLt storageSlot mapSlot k
    · have hOnlyUpNZ : onlyUpWordOf s != 0 := by simpa using hOnlyUp0
      exact setRoundDataSafe_zero_history_onlyup_on_writes data dataTimestamp growthApr blockTimestamp s
        hLastUpdated0 hOnlyUp0 (hOnlyUpApr hOnlyUpNZ) hTimeOrder hTimeGap hStarted hDataLo hDataHi
        hGrowthLo hGrowthHi hDataTsLt storageSlot mapSlot k
  · have hLastUpdatedNZ : lastTimestampOf s != 0 := by simpa using hLastUpdated0
    have hPrevStarted' : lastStartedAtOf s <= blockTimestamp := hPrevStarted hLastUpdatedNZ
    have hDataTsLe' : dataTimestamp <= blockTimestamp := hDataTsLe hLastUpdatedNZ
    have hDeviationCap' :
        deviationOfSafeCall data dataTimestamp growthApr blockTimestamp s <= maxAnswerDeviationOf s :=
      hDeviationCap hLastUpdatedNZ
    by_cases hCandidateZero' : candidateLivePrice data dataTimestamp growthApr blockTimestamp = 0
    · by_cases hOnlyUp0 : onlyUpWordOf s = 0
      · exact setRoundDataSafe_candidate_zero_onlyup_off_writes data dataTimestamp growthApr blockTimestamp s
          hLastUpdated0 hPrevStarted' hDataTsLe' hDeviationCap' hCandidateZero' hOnlyUp0
          hTimeOrder hTimeGap hStarted hDataLo hDataHi hGrowthLo hGrowthHi hDataTsLt storageSlot mapSlot k
      · have hOnlyUpNZ : onlyUpWordOf s != 0 := by simpa using hOnlyUp0
        exact setRoundDataSafe_candidate_zero_onlyup_on_writes data dataTimestamp growthApr blockTimestamp s
          hLastUpdated0 hPrevStarted' hDataTsLe' hDeviationCap' hCandidateZero' hOnlyUp0
          (hOnlyUpApr hOnlyUpNZ) hTimeOrder hTimeGap hStarted hDataLo hDataHi hGrowthLo hGrowthHi
          hDataTsLt storageSlot mapSlot k
    · have hLastAnswerNZ' : lastAnswerOf s blockTimestamp != 0 :=
        hLastAnswerNZ hLastUpdatedNZ hCandidateZero'
      by_cases hOnlyUp0 : onlyUpWordOf s = 0
      · exact setRoundDataSafe_candidate_nonzero_onlyup_off_writes data dataTimestamp growthApr blockTimestamp s
          hLastUpdated0 hPrevStarted' hDataTsLe' hLastAnswerNZ' hDeviationCap' hCandidateZero' hOnlyUp0
          hTimeOrder hTimeGap hStarted hDataLo hDataHi hGrowthLo hGrowthHi hDataTsLt storageSlot mapSlot k
      · have hOnlyUpNZ : onlyUpWordOf s != 0 := by simpa using hOnlyUp0
        exact setRoundDataSafe_candidate_nonzero_onlyup_on_writes data dataTimestamp growthApr blockTimestamp s
          hLastUpdated0 hPrevStarted' hDataTsLe' hLastAnswerNZ'
          (hOnlyUpDeviation hLastUpdatedNZ hOnlyUpNZ) hDeviationCap' hCandidateZero' hOnlyUp0
          (hOnlyUpApr hOnlyUpNZ) hTimeOrder hTimeGap hStarted hDataLo hDataHi hGrowthLo hGrowthHi
          hDataTsLt storageSlot mapSlot k

private theorem setRoundDataSafe_writes_latestRound
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hPrevStarted : lastTimestampOf s != 0 → lastStartedAtOf s <= blockTimestamp)
    (hDataTsLe : lastTimestampOf s != 0 → dataTimestamp <= blockTimestamp)
    (hLastAnswerNZ :
      lastTimestampOf s != 0 → candidateLivePrice data dataTimestamp growthApr blockTimestamp ≠ 0 →
        lastAnswerOf s blockTimestamp != 0)
    (hOnlyUpDeviation :
      lastTimestampOf s != 0 → onlyUpWordOf s != 0 →
        slt (signedDeviationOfSafeCall data dataTimestamp growthApr blockTimestamp s) 0 = false)
    (hDeviationCap :
      lastTimestampOf s != 0 →
        deviationOfSafeCall data dataTimestamp growthApr blockTimestamp s <= maxAnswerDeviationOf s)
    (hOnlyUpApr : onlyUpWordOf s != 0 → slt growthApr 0 = false)
    (hTimeOrder : lastTimestampOf s <= blockTimestamp)
    (hTimeGap : sub blockTimestamp (lastTimestampOf s) > 3600)
    (hStarted : dataTimestamp > lastStartedAtOf s)
    (hDataLo : slt data (minAnswerOf s) = false)
    (hDataHi : sgt data (maxAnswerOf s) = false)
    (hGrowthLo : slt growthApr (minGrowthAprOf s) = false)
    (hGrowthHi : sgt growthApr (maxGrowthAprOf s) = false)
    (hDataTsLt : dataTimestamp < blockTimestamp) :
    let s' := ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd
    latestRoundOf s' = nextRoundIdOf s := by
  dsimp [latestRoundOf]
  have hWrites := setRoundDataSafe_projected_writes data dataTimestamp growthApr blockTimestamp s
    hPrevStarted hDataTsLe hLastAnswerNZ hOnlyUpDeviation hDeviationCap hOnlyUpApr
    hTimeOrder hTimeGap hStarted hDataLo hDataHi hGrowthLo hGrowthHi hDataTsLt
    CustomFeedGrowthSafe.latestRound.slot 0 0
  simpa [writeStorageAfterRound, nextRoundIdOf, latestRoundOf] using hWrites.1

private theorem setRoundDataSafe_writes_answer
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hPrevStarted : lastTimestampOf s != 0 → lastStartedAtOf s <= blockTimestamp)
    (hDataTsLe : lastTimestampOf s != 0 → dataTimestamp <= blockTimestamp)
    (hLastAnswerNZ :
      lastTimestampOf s != 0 → candidateLivePrice data dataTimestamp growthApr blockTimestamp ≠ 0 →
        lastAnswerOf s blockTimestamp != 0)
    (hOnlyUpDeviation :
      lastTimestampOf s != 0 → onlyUpWordOf s != 0 →
        slt (signedDeviationOfSafeCall data dataTimestamp growthApr blockTimestamp s) 0 = false)
    (hDeviationCap :
      lastTimestampOf s != 0 →
        deviationOfSafeCall data dataTimestamp growthApr blockTimestamp s <= maxAnswerDeviationOf s)
    (hOnlyUpApr : onlyUpWordOf s != 0 → slt growthApr 0 = false)
    (hTimeOrder : lastTimestampOf s <= blockTimestamp)
    (hTimeGap : sub blockTimestamp (lastTimestampOf s) > 3600)
    (hStarted : dataTimestamp > lastStartedAtOf s)
    (hDataLo : slt data (minAnswerOf s) = false)
    (hDataHi : sgt data (maxAnswerOf s) = false)
    (hGrowthLo : slt growthApr (minGrowthAprOf s) = false)
    (hGrowthHi : sgt growthApr (maxGrowthAprOf s) = false)
    (hDataTsLt : dataTimestamp < blockTimestamp) :
    let s' := ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd
    roundAnswerOf s' (nextRoundIdOf s) = data := by
  dsimp [roundAnswerOf]
  have hWrites := setRoundDataSafe_projected_writes data dataTimestamp growthApr blockTimestamp s
    hPrevStarted hDataTsLe hLastAnswerNZ hOnlyUpDeviation hDeviationCap hOnlyUpApr
    hTimeOrder hTimeGap hStarted hDataLo hDataHi hGrowthLo hGrowthHi hDataTsLt
    0 CustomFeedGrowthSafe.roundAnswer.slot (nextRoundIdOf s)
  simpa [writeMapUintAfterRound, nextRoundIdOf, roundAnswerSlot, roundStartedAtSlot,
    roundUpdatedAtSlot, roundGrowthAprSlot] using hWrites.2

private theorem setRoundDataSafe_writes_startedAt
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hPrevStarted : lastTimestampOf s != 0 → lastStartedAtOf s <= blockTimestamp)
    (hDataTsLe : lastTimestampOf s != 0 → dataTimestamp <= blockTimestamp)
    (hLastAnswerNZ :
      lastTimestampOf s != 0 → candidateLivePrice data dataTimestamp growthApr blockTimestamp ≠ 0 →
        lastAnswerOf s blockTimestamp != 0)
    (hOnlyUpDeviation :
      lastTimestampOf s != 0 → onlyUpWordOf s != 0 →
        slt (signedDeviationOfSafeCall data dataTimestamp growthApr blockTimestamp s) 0 = false)
    (hDeviationCap :
      lastTimestampOf s != 0 →
        deviationOfSafeCall data dataTimestamp growthApr blockTimestamp s <= maxAnswerDeviationOf s)
    (hOnlyUpApr : onlyUpWordOf s != 0 → slt growthApr 0 = false)
    (hTimeOrder : lastTimestampOf s <= blockTimestamp)
    (hTimeGap : sub blockTimestamp (lastTimestampOf s) > 3600)
    (hStarted : dataTimestamp > lastStartedAtOf s)
    (hDataLo : slt data (minAnswerOf s) = false)
    (hDataHi : sgt data (maxAnswerOf s) = false)
    (hGrowthLo : slt growthApr (minGrowthAprOf s) = false)
    (hGrowthHi : sgt growthApr (maxGrowthAprOf s) = false)
    (hDataTsLt : dataTimestamp < blockTimestamp) :
    let s' := ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd
    roundStartedAtOf s' (nextRoundIdOf s) = dataTimestamp := by
  dsimp [roundStartedAtOf]
  have hWrites := setRoundDataSafe_projected_writes data dataTimestamp growthApr blockTimestamp s
    hPrevStarted hDataTsLe hLastAnswerNZ hOnlyUpDeviation hDeviationCap hOnlyUpApr
    hTimeOrder hTimeGap hStarted hDataLo hDataHi hGrowthLo hGrowthHi hDataTsLt
    0 CustomFeedGrowthSafe.roundStartedAt.slot (nextRoundIdOf s)
  simpa [writeMapUintAfterRound, nextRoundIdOf, roundAnswerSlot, roundStartedAtSlot,
    roundUpdatedAtSlot, roundGrowthAprSlot] using hWrites.2

private theorem setRoundDataSafe_writes_growthApr
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hPrevStarted : lastTimestampOf s != 0 → lastStartedAtOf s <= blockTimestamp)
    (hDataTsLe : lastTimestampOf s != 0 → dataTimestamp <= blockTimestamp)
    (hLastAnswerNZ :
      lastTimestampOf s != 0 → candidateLivePrice data dataTimestamp growthApr blockTimestamp ≠ 0 →
        lastAnswerOf s blockTimestamp != 0)
    (hOnlyUpDeviation :
      lastTimestampOf s != 0 → onlyUpWordOf s != 0 →
        slt (signedDeviationOfSafeCall data dataTimestamp growthApr blockTimestamp s) 0 = false)
    (hDeviationCap :
      lastTimestampOf s != 0 →
        deviationOfSafeCall data dataTimestamp growthApr blockTimestamp s <= maxAnswerDeviationOf s)
    (hOnlyUpApr : onlyUpWordOf s != 0 → slt growthApr 0 = false)
    (hTimeOrder : lastTimestampOf s <= blockTimestamp)
    (hTimeGap : sub blockTimestamp (lastTimestampOf s) > 3600)
    (hStarted : dataTimestamp > lastStartedAtOf s)
    (hDataLo : slt data (minAnswerOf s) = false)
    (hDataHi : sgt data (maxAnswerOf s) = false)
    (hGrowthLo : slt growthApr (minGrowthAprOf s) = false)
    (hGrowthHi : sgt growthApr (maxGrowthAprOf s) = false)
    (hDataTsLt : dataTimestamp < blockTimestamp) :
    let s' := ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd
    roundGrowthAprOf s' (nextRoundIdOf s) = growthApr := by
  dsimp [roundGrowthAprOf]
  have hWrites := setRoundDataSafe_projected_writes data dataTimestamp growthApr blockTimestamp s
    hPrevStarted hDataTsLe hLastAnswerNZ hOnlyUpDeviation hDeviationCap hOnlyUpApr
    hTimeOrder hTimeGap hStarted hDataLo hDataHi hGrowthLo hGrowthHi hDataTsLt
    0 CustomFeedGrowthSafe.roundGrowthApr.slot (nextRoundIdOf s)
  simpa [writeMapUintAfterRound, nextRoundIdOf, roundAnswerSlot, roundStartedAtSlot,
    roundUpdatedAtSlot, roundGrowthAprSlot] using hWrites.2

private theorem setRoundDataSafe_rejects_zero_price_prev_started_data_ts_le
    (dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hLastUpdated : lastTimestampOf s != 0)
    (hMaxDev : maxAnswerDeviationOf s < HUNDRED_ONE)
    (hPrevStarted : lastStartedAtOf s <= blockTimestamp)
    (hDataTsLe : dataTimestamp <= blockTimestamp) :
    setRoundDataSafe_rejects_zero_price_spec dataTimestamp growthApr blockTimestamp s := by
  unfold setRoundDataSafe_rejects_zero_price_spec safeRejected safeCallResult
  have hZeroMul :
      mul (mul 0 (sub blockTimestamp dataTimestamp)) growthApr = 0 := by
    simp [Verity.Core.Uint256.mul]
  have hZeroPriceNum :
      add 0 (sdiv (mul (mul 0 (sub blockTimestamp dataTimestamp)) growthApr) 315360000000000000) = 0 := by
    rw [hZeroMul]
    native_decide
  have hZeroPriceNumDenom :
      add 0 (sdiv (mul (mul 0 (sub blockTimestamp dataTimestamp)) growthApr) GROWTH_DENOMINATOR) = 0 := by
    simpa [GROWTH_DENOMINATOR, HUNDRED_ONE, ONE, YEAR_SECONDS] using hZeroPriceNum
  have hOnlyUpEval :
      (getStorage CustomFeedGrowthSafe.onlyUp).run s =
        ContractResult.success (onlyUpWordOf s) s := by
    simp [onlyUpWordOf, onlyUpSlot, getStorage, Contract.run]
  have hLastUpdatedEval :
      (CustomFeedGrowthSafe.lastTimestamp.run s) =
        ContractResult.success (lastTimestampOf s) s := by
    exact lastTimestamp_eval s
  have hLastUpdatedNZBranch : ((lastTimestampOf s != 0) = true) := by
    simpa using hLastUpdated
  have hNoCap : ¬ 10000000000 <= maxAnswerDeviationOf s := by
    simpa [HUNDRED_ONE] using hMaxDev
  have hLastAnswerEval :
      ((CustomFeedGrowthSafe.lastAnswer blockTimestamp).run s) =
        ContractResult.success (lastAnswerOf s blockTimestamp) s := by
    exact lastAnswer_eval blockTimestamp s hPrevStarted
  have hCandidateEval :
      ((CustomFeedGrowthSafe.applyGrowth 0 growthApr dataTimestamp blockTimestamp).run s) =
        ContractResult.success 0 s := by
    have hCandidateEvalBase :
        ((CustomFeedGrowthSafe.applyGrowth 0 growthApr dataTimestamp blockTimestamp).run s) =
          ContractResult.success
            (add 0 (sdiv (mul (mul 0 (sub blockTimestamp dataTimestamp)) growthApr) GROWTH_DENOMINATOR)) s := by
      simpa [applyGrowthNowRaw, applyGrowthAtRaw] using
        (applyGrowth_eval 0 growthApr dataTimestamp blockTimestamp s hDataTsLe)
    simpa [hZeroPriceNumDenom] using hCandidateEvalBase
  have hDeviationEval :
      ((CustomFeedGrowthSafe._getDeviation (lastAnswerOf s blockTimestamp) 0 (onlyUpWordOf s != 0)).run s) =
        ContractResult.success HUNDRED_ONE s := by
    simp [CustomFeedGrowthSafe._getDeviation, Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run]
  have hMaxDeviationEval :
      (getStorage CustomFeedGrowthSafe.maxAnswerDeviation).run s =
        ContractResult.success (maxAnswerDeviationOf s) s := by
    simp [maxAnswerDeviationOf, maxAnswerDeviationSlot, getStorage, Contract.run]
  have hNoCapBranch : decide (HUNDRED_ONE ≤ maxAnswerDeviationOf s) = false := by
    simpa [HUNDRED_ONE] using hNoCap
  unfold CustomFeedGrowthSafe.setRoundDataSafe Verity.require
  simp only [Bind.bind]
  rw [bind_run_success_same_state _ _ _ _ hOnlyUpEval]
  rw [bind_run_success_same_state _ _ _ _ hLastUpdatedEval]
  rw [if_pos hLastUpdatedNZBranch]
  rw [bind_run_success_same_state _ _ _ _ hLastAnswerEval]
  rw [bind_run_success_same_state _ _ _ _ hCandidateEval]
  rw [bind_run_success_same_state _ _ _ _ hDeviationEval]
  rw [bind_run_success_same_state _ _ _ _ hMaxDeviationEval]
  rw [hNoCapBranch]
  simp [Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run,
    ContractResult.isSuccess, HUNDRED_ONE]

private theorem setRoundDataSafe_rejects_zero_price_prev_started_data_ts_gt
    (dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hLastUpdated : lastTimestampOf s != 0)
    (hPrevStarted : lastStartedAtOf s <= blockTimestamp)
    (hDataTsLe : ¬ dataTimestamp <= blockTimestamp) :
    setRoundDataSafe_rejects_zero_price_spec dataTimestamp growthApr blockTimestamp s := by
  unfold setRoundDataSafe_rejects_zero_price_spec safeRejected safeCallResult
  have hOnlyUpEval :
      (getStorage CustomFeedGrowthSafe.onlyUp).run s =
        ContractResult.success (onlyUpWordOf s) s := by
    simp [onlyUpWordOf, onlyUpSlot, getStorage, Contract.run]
  have hLastUpdatedEval :
      (CustomFeedGrowthSafe.lastTimestamp.run s) =
        ContractResult.success (lastTimestampOf s) s := by
    exact lastTimestamp_eval s
  have hLastUpdatedNZBranch : ((lastTimestampOf s != 0) = true) := by
    simpa using hLastUpdated
  have hLastAnswerEval :
      ((CustomFeedGrowthSafe.lastAnswer blockTimestamp).run s) =
        ContractResult.success (lastAnswerOf s blockTimestamp) s := by
    exact lastAnswer_eval blockTimestamp s hPrevStarted
  have hCandidateRevert :
      ((CustomFeedGrowthSafe.applyGrowth 0 growthApr dataTimestamp blockTimestamp).run s) =
        ContractResult.revert "CAG: timestampTo < timestampFrom" s := by
    exact applyGrowth_revert 0 growthApr dataTimestamp blockTimestamp s hDataTsLe
  unfold CustomFeedGrowthSafe.setRoundDataSafe Verity.require
  simp only [Bind.bind]
  rw [bind_run_success_same_state _ _ _ _ hOnlyUpEval]
  rw [bind_run_success_same_state _ _ _ _ hLastUpdatedEval]
  rw [if_pos hLastUpdatedNZBranch]
  rw [bind_run_success_same_state _ _ _ _ hLastAnswerEval]
  rw [bind_run_revert_same_state _ _ _ _ hCandidateRevert]
  simp [ContractResult.isSuccess]

private theorem setRoundDataSafe_rejects_zero_price_prev_started_gt
    (dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hLastUpdated : lastTimestampOf s != 0)
    (hPrevStarted : ¬ lastStartedAtOf s <= blockTimestamp) :
    setRoundDataSafe_rejects_zero_price_spec dataTimestamp growthApr blockTimestamp s := by
  unfold setRoundDataSafe_rejects_zero_price_spec safeRejected safeCallResult
  have hOnlyUpEval :
      (getStorage CustomFeedGrowthSafe.onlyUp).run s =
        ContractResult.success (onlyUpWordOf s) s := by
    simp [onlyUpWordOf, onlyUpSlot, getStorage, Contract.run]
  have hLastUpdatedEval :
      (CustomFeedGrowthSafe.lastTimestamp.run s) =
        ContractResult.success (lastTimestampOf s) s := by
    exact lastTimestamp_eval s
  have hLastUpdatedNZBranch : ((lastTimestampOf s != 0) = true) := by
    simpa using hLastUpdated
  have hLastAnswerRevert :
      ((CustomFeedGrowthSafe.lastAnswer blockTimestamp).run s) =
        ContractResult.revert "CAG: timestampTo < timestampFrom" s := by
    exact lastAnswer_revert blockTimestamp s hPrevStarted
  unfold CustomFeedGrowthSafe.setRoundDataSafe Verity.require
  simp only [Bind.bind]
  rw [bind_run_success_same_state _ _ _ _ hOnlyUpEval]
  rw [bind_run_success_same_state _ _ _ _ hLastUpdatedEval]
  rw [if_pos hLastUpdatedNZBranch]
  rw [bind_run_revert_same_state _ _ _ _ hLastAnswerRevert]
  simp [ContractResult.isSuccess]

theorem setRoundDataSafe_rejects_zero_price
    (dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hLatest : latestRoundOf s >= 1)
    (hLastUpdated : lastTimestampOf s != 0)
    (hMaxDev : maxAnswerDeviationOf s < HUNDRED_ONE) :
    setRoundDataSafe_rejects_zero_price_spec dataTimestamp growthApr blockTimestamp s := by
  let _ := hLatest
  by_cases hPrevStarted : lastStartedAtOf s <= blockTimestamp
  · by_cases hDataTsLe : dataTimestamp <= blockTimestamp
    · exact setRoundDataSafe_rejects_zero_price_prev_started_data_ts_le
        dataTimestamp growthApr blockTimestamp s hLastUpdated hMaxDev hPrevStarted hDataTsLe
    · exact setRoundDataSafe_rejects_zero_price_prev_started_data_ts_gt
        dataTimestamp growthApr blockTimestamp s hLastUpdated hPrevStarted hDataTsLe
  · exact setRoundDataSafe_rejects_zero_price_prev_started_gt
      dataTimestamp growthApr blockTimestamp s hLastUpdated hPrevStarted

theorem setRoundDataSafe_deviation_bound
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hLatest : latestRoundOf s >= 1)
    (hLastUpdated : lastTimestampOf s != 0)
    (hDeviation :
      deviationOfSafeCall data dataTimestamp growthApr blockTimestamp s <= maxAnswerDeviationOf s) :
    let s' := ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd
    setRoundDataSafe_deviation_bound_spec data dataTimestamp growthApr blockTimestamp s s' := by
  let _ := hLatest
  let _ := hLastUpdated
  simpa [setRoundDataSafe_deviation_bound_spec, withinDeviationBound] using hDeviation

theorem setRoundDataSafe_enforces_time_gap
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hTimeOrder : lastTimestampOf s <= blockTimestamp)
    (hTimeGap : sub blockTimestamp (lastTimestampOf s) > 3600) :
    let s' := ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd
    setRoundDataSafe_enforces_time_gap_spec blockTimestamp s s' := by
  unfold setRoundDataSafe_enforces_time_gap_spec respectsTimeGap
  have hTimeOrder' : (lastTimestampOf s : Nat) ≤ (blockTimestamp : Nat) := by
    simpa using hTimeOrder
  have hGap' : ((sub blockTimestamp (lastTimestampOf s) : Uint256) : Nat) > 3600 := by
    simpa using hTimeGap
  rw [Verity.EVM.Uint256.sub_eq_of_le hTimeOrder'] at hGap'
  simpa using hGap'

theorem setRoundDataSafe_startedAt_monotonic
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hPrevStarted : lastTimestampOf s != 0 → lastStartedAtOf s <= blockTimestamp)
    (hDataTsLe : lastTimestampOf s != 0 → dataTimestamp <= blockTimestamp)
    (hLastAnswerNZ :
      lastTimestampOf s != 0 → candidateLivePrice data dataTimestamp growthApr blockTimestamp ≠ 0 →
        lastAnswerOf s blockTimestamp != 0)
    (hOnlyUpDeviation :
      lastTimestampOf s != 0 → onlyUpWordOf s != 0 →
        slt (signedDeviationOfSafeCall data dataTimestamp growthApr blockTimestamp s) 0 = false)
    (hDeviationCap :
      lastTimestampOf s != 0 →
        deviationOfSafeCall data dataTimestamp growthApr blockTimestamp s <= maxAnswerDeviationOf s)
    (hOnlyUpApr : onlyUpWordOf s != 0 → slt growthApr 0 = false)
    (hTimeOrder : lastTimestampOf s <= blockTimestamp)
    (hTimeGap : sub blockTimestamp (lastTimestampOf s) > 3600)
    (hStarted : dataTimestamp > lastStartedAtOf s)
    (hDataLo : slt data (minAnswerOf s) = false)
    (hDataHi : sgt data (maxAnswerOf s) = false)
    (hGrowthLo : slt growthApr (minGrowthAprOf s) = false)
    (hGrowthHi : sgt growthApr (maxGrowthAprOf s) = false)
    (hDataTsLt : dataTimestamp < blockTimestamp) :
    let s' := ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd
    setRoundDataSafe_startedAt_monotonic_spec data dataTimestamp growthApr blockTimestamp s s' := by
  unfold setRoundDataSafe_startedAt_monotonic_spec
  dsimp
  rw [setRoundDataSafe_writes_latestRound data dataTimestamp growthApr blockTimestamp s
    hPrevStarted hDataTsLe hLastAnswerNZ hOnlyUpDeviation hDeviationCap hOnlyUpApr
    hTimeOrder hTimeGap hStarted hDataLo hDataHi hGrowthLo hGrowthHi hDataTsLt]
  rw [setRoundDataSafe_writes_startedAt data dataTimestamp growthApr blockTimestamp s
    hPrevStarted hDataTsLe hLastAnswerNZ hOnlyUpDeviation hDeviationCap hOnlyUpApr
    hTimeOrder hTimeGap hStarted hDataLo hDataHi hGrowthLo hGrowthHi hDataTsLt]
  exact hStarted

theorem setRoundDataSafe_onlyUp_nonnegative_deviation
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hLatest : latestRoundOf s >= 1)
    (hLastUpdated : lastTimestampOf s != 0)
    (hOnlyUpDeviation :
      (onlyUpWordOf s != 0) = true →
        slt (signedDeviationOfSafeCall data dataTimestamp growthApr blockTimestamp s) 0 = false) :
    let s' := ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd
    setRoundDataSafe_onlyUp_nonnegative_deviation_spec data dataTimestamp growthApr blockTimestamp s s' := by
  let _ := hLatest
  let _ := hLastUpdated
  simpa [setRoundDataSafe_onlyUp_nonnegative_deviation_spec, respectsOnlyUp] using hOnlyUpDeviation

theorem setRoundDataSafe_propagates_band_guard
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hPrevStarted : lastTimestampOf s != 0 → lastStartedAtOf s <= blockTimestamp)
    (hDataTsLe : lastTimestampOf s != 0 → dataTimestamp <= blockTimestamp)
    (hLastAnswerNZ :
      lastTimestampOf s != 0 → candidateLivePrice data dataTimestamp growthApr blockTimestamp ≠ 0 →
        lastAnswerOf s blockTimestamp != 0)
    (hOnlyUpDeviation :
      lastTimestampOf s != 0 → onlyUpWordOf s != 0 →
        slt (signedDeviationOfSafeCall data dataTimestamp growthApr blockTimestamp s) 0 = false)
    (hDeviationCap :
      lastTimestampOf s != 0 →
        deviationOfSafeCall data dataTimestamp growthApr blockTimestamp s <= maxAnswerDeviationOf s)
    (hOnlyUpApr : onlyUpWordOf s != 0 → slt growthApr 0 = false)
    (hTimeOrder : lastTimestampOf s <= blockTimestamp)
    (hTimeGap : sub blockTimestamp (lastTimestampOf s) > 3600)
    (hStarted : dataTimestamp > lastStartedAtOf s)
    (hDataLo : slt data (minAnswerOf s) = false)
    (hDataHi : sgt data (maxAnswerOf s) = false)
    (hGrowthLo : slt growthApr (minGrowthAprOf s) = false)
    (hGrowthHi : sgt growthApr (maxGrowthAprOf s) = false)
    (hDataTsLt : dataTimestamp < blockTimestamp) :
    let s' := ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd
    setRoundDataSafe_propagates_band_guard_spec data dataTimestamp growthApr blockTimestamp s s' := by
  unfold setRoundDataSafe_propagates_band_guard_spec answerInRange aprInRange
  dsimp
  rw [setRoundDataSafe_writes_latestRound data dataTimestamp growthApr blockTimestamp s
    hPrevStarted hDataTsLe hLastAnswerNZ hOnlyUpDeviation hDeviationCap hOnlyUpApr
    hTimeOrder hTimeGap hStarted hDataLo hDataHi hGrowthLo hGrowthHi hDataTsLt]
  rw [setRoundDataSafe_writes_answer data dataTimestamp growthApr blockTimestamp s
    hPrevStarted hDataTsLe hLastAnswerNZ hOnlyUpDeviation hDeviationCap hOnlyUpApr
    hTimeOrder hTimeGap hStarted hDataLo hDataHi hGrowthLo hGrowthHi hDataTsLt]
  rw [setRoundDataSafe_writes_growthApr data dataTimestamp growthApr blockTimestamp s
    hPrevStarted hDataTsLe hLastAnswerNZ hOnlyUpDeviation hDeviationCap hOnlyUpApr
    hTimeOrder hTimeGap hStarted hDataLo hDataHi hGrowthLo hGrowthHi hDataTsLt]
  exact ⟨⟨hDataLo, hDataHi⟩, ⟨hGrowthLo, hGrowthHi⟩⟩

theorem setRoundDataSafe_writes_submitted_round
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hPrevStarted : lastTimestampOf s != 0 → lastStartedAtOf s <= blockTimestamp)
    (hDataTsLe : lastTimestampOf s != 0 → dataTimestamp <= blockTimestamp)
    (hLastAnswerNZ :
      lastTimestampOf s != 0 → candidateLivePrice data dataTimestamp growthApr blockTimestamp ≠ 0 →
        lastAnswerOf s blockTimestamp != 0)
    (hOnlyUpDeviation :
      lastTimestampOf s != 0 → onlyUpWordOf s != 0 →
        slt (signedDeviationOfSafeCall data dataTimestamp growthApr blockTimestamp s) 0 = false)
    (hDeviationCap :
      lastTimestampOf s != 0 →
        deviationOfSafeCall data dataTimestamp growthApr blockTimestamp s <= maxAnswerDeviationOf s)
    (hOnlyUpApr : onlyUpWordOf s != 0 → slt growthApr 0 = false)
    (hTimeOrder : lastTimestampOf s <= blockTimestamp)
    (hTimeGap : sub blockTimestamp (lastTimestampOf s) > 3600)
    (hStarted : dataTimestamp > lastStartedAtOf s)
    (hDataLo : slt data (minAnswerOf s) = false)
    (hDataHi : sgt data (maxAnswerOf s) = false)
    (hGrowthLo : slt growthApr (minGrowthAprOf s) = false)
    (hGrowthHi : sgt growthApr (maxGrowthAprOf s) = false)
    (hDataTsLt : dataTimestamp < blockTimestamp) :
    let s' := ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd
    writesSubmittedRound data dataTimestamp growthApr blockTimestamp s s' := by
  unfold writesSubmittedRound
  dsimp
  have hLatest := setRoundDataSafe_writes_latestRound data dataTimestamp growthApr blockTimestamp s
    hPrevStarted hDataTsLe hLastAnswerNZ hOnlyUpDeviation hDeviationCap hOnlyUpApr
    hTimeOrder hTimeGap hStarted hDataLo hDataHi hGrowthLo hGrowthHi hDataTsLt
  have hAnswer := setRoundDataSafe_writes_answer data dataTimestamp growthApr blockTimestamp s
    hPrevStarted hDataTsLe hLastAnswerNZ hOnlyUpDeviation hDeviationCap hOnlyUpApr
    hTimeOrder hTimeGap hStarted hDataLo hDataHi hGrowthLo hGrowthHi hDataTsLt
  have hStartedAt := setRoundDataSafe_writes_startedAt data dataTimestamp growthApr blockTimestamp s
    hPrevStarted hDataTsLe hLastAnswerNZ hOnlyUpDeviation hDeviationCap hOnlyUpApr
    hTimeOrder hTimeGap hStarted hDataLo hDataHi hGrowthLo hGrowthHi hDataTsLt
  have hGrowth := setRoundDataSafe_writes_growthApr data dataTimestamp growthApr blockTimestamp s
    hPrevStarted hDataTsLe hLastAnswerNZ hOnlyUpDeviation hDeviationCap hOnlyUpApr
    hTimeOrder hTimeGap hStarted hDataLo hDataHi hGrowthLo hGrowthHi hDataTsLt
  have hUpdatedWrites := setRoundDataSafe_projected_writes data dataTimestamp growthApr blockTimestamp s
    hPrevStarted hDataTsLe hLastAnswerNZ hOnlyUpDeviation hDeviationCap hOnlyUpApr
    hTimeOrder hTimeGap hStarted hDataLo hDataHi hGrowthLo hGrowthHi hDataTsLt
    0 CustomFeedGrowthSafe.roundUpdatedAt.slot (nextRoundIdOf s)
  have hUpdated :
      roundUpdatedAtOf
          (((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd)
          (nextRoundIdOf s) =
        blockTimestamp := by
    simpa [roundUpdatedAtOf, writeMapUintAfterRound, nextRoundIdOf, roundAnswerSlot, roundStartedAtSlot,
      roundUpdatedAtSlot, roundGrowthAprSlot] using hUpdatedWrites.2
  refine ⟨hLatest, ?_, ?_, ?_, ?_⟩
  · rw [hLatest]
    exact hAnswer
  · rw [hLatest]
    exact hStartedAt
  · rw [hLatest]
    exact hUpdated
  · rw [hLatest]
    exact hGrowth

theorem setRoundDataSafe_zero_rejected_under_strict_deviation
    (dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hLatest : latestRoundOf s >= 1) :
    zeroRejectedUnderStrictDeviation dataTimestamp growthApr blockTimestamp s := by
  unfold zeroRejectedUnderStrictDeviation hasHistory
  intro hGuard
  exact setRoundDataSafe_rejects_zero_price dataTimestamp growthApr blockTimestamp s
    hLatest hGuard.1 hGuard.2

private theorem latestRound_ne_nextRoundId (s : ContractState) :
    latestRoundOf s ≠ nextRoundIdOf s := by
  intro hEq
  unfold nextRoundIdOf at hEq
  have hValEq : (latestRoundOf s : Nat) = (add (latestRoundOf s) 1).val := by
    simpa using congrArg (fun x : Uint256 => x.val) hEq
  by_cases hMax : (latestRoundOf s : Nat) = Verity.Core.MAX_UINT256
  · have hWrap :
        (add (latestRoundOf s) 1).val = 0 := by
      have hWrapNat :
          (((latestRoundOf s : Nat) + 1) % Verity.Core.Uint256.modulus) = 0 := by
        rw [hMax, Verity.Core.Uint256.max_uint256_succ_eq_modulus, Nat.mod_self]
      simpa [Verity.Core.Uint256.add, Verity.Core.Uint256.ofNat] using hWrapNat
    rw [hWrap] at hValEq
    have hLatestPos : (latestRoundOf s : Nat) ≠ 0 := by
      rw [hMax]
      decide
    exact hLatestPos hValEq
  · have hLtMod :
        (latestRoundOf s : Nat) + 1 < Verity.Core.Uint256.modulus := by
      have hLeMax := Verity.Core.Uint256.val_le_max (latestRoundOf s)
      have hLtMax : (latestRoundOf s : Nat) < Verity.Core.MAX_UINT256 := by
        exact Nat.lt_of_le_of_ne hLeMax hMax
      rw [← Verity.Core.Uint256.max_uint256_succ_eq_modulus]
      exact Nat.succ_lt_succ hLtMax
    have hAddVal :
        (add (latestRoundOf s) 1).val = (latestRoundOf s : Nat) + 1 := by
      simpa [Verity.Core.Uint256.add, Verity.Core.Uint256.ofNat] using
        (Nat.mod_eq_of_lt hLtMod)
    rw [hAddVal] at hValEq
    exact Nat.ne_of_lt (Nat.lt_succ_self (latestRoundOf s).val) hValEq

private theorem setRoundDataSafe_accepted_or_rejected
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState) :
    safeAccepted data dataTimestamp growthApr blockTimestamp s ∨
      safeRejected data dataTimestamp growthApr blockTimestamp s := by
  unfold safeAccepted safeRejected safeCallResult
  cases hRun : (CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s <;>
    simp [ContractResult.isSuccess, hRun]

private theorem safeRejected_snd_eq
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hRejected : safeRejected data dataTimestamp growthApr blockTimestamp s) :
    (safeCallResult data dataTimestamp growthApr blockTimestamp s).snd = s := by
  unfold safeRejected at hRejected
  unfold safeCallResult Contract.run at hRejected ⊢
  cases hRaw : CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp s <;>
    simp [ContractResult.isSuccess, hRaw] at hRejected ⊢

private theorem setRoundData_success_implies_inputs
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hAccepted :
      ((CustomFeedGrowthSafe.setRoundData data dataTimestamp growthApr blockTimestamp).run s).isSuccess =
        true) :
    answerInRange data s ∧
      aprInRange growthApr s ∧
      submittedTimestampBeforeCurrentTime dataTimestamp blockTimestamp := by
  have hMinEval :
      (getStorage CustomFeedGrowthSafe.minAnswer).run s =
        ContractResult.success (minAnswerOf s) s := by
    simp [minAnswerOf, minAnswerSlot, getStorage, Contract.run]
  have hMaxEval :
      (getStorage CustomFeedGrowthSafe.maxAnswer).run s =
        ContractResult.success (maxAnswerOf s) s := by
    simp [maxAnswerOf, maxAnswerSlot, getStorage, Contract.run]
  have hMinGrowthEval :
      (getStorage CustomFeedGrowthSafe.minGrowthApr).run s =
        ContractResult.success (minGrowthAprOf s) s := by
    simp [minGrowthAprOf, minGrowthAprSlot, getStorage, Contract.run]
  have hMaxGrowthEval :
      (getStorage CustomFeedGrowthSafe.maxGrowthApr).run s =
        ContractResult.success (maxGrowthAprOf s) s := by
    simp [maxGrowthAprOf, maxGrowthAprSlot, getStorage, Contract.run]
  have hLatestEval :
      (getStorage CustomFeedGrowthSafe.latestRound).run s =
        ContractResult.success (latestRoundOf s) s := by
    simp [latestRoundOf, latestRoundSlot, getStorage, Contract.run]
  have hBase := hAccepted
  unfold CustomFeedGrowthSafe.setRoundData at hBase
  simp only [Bind.bind] at hBase
  rw [bind_run_success_same_state _ _ _ _ hMinEval] at hBase
  rw [bind_run_success_same_state _ _ _ _ hMaxEval] at hBase
  rw [bind_run_success_same_state _ _ _ _ hMinGrowthEval] at hBase
  rw [bind_run_success_same_state _ _ _ _ hMaxGrowthEval] at hBase
  rw [bind_run_success_same_state _ _ _ _ hLatestEval] at hBase

  have hDataLo : slt data (minAnswerOf s) = false := by
    by_cases hLo : slt data (minAnswerOf s) = true
    · have hBranch := hBase
      rw [hLo] at hBranch
      simp [Verity.bind, Bind.bind, Verity.pure, Pure.pure, Verity.require, Contract.run] at hBranch
    · cases hBool : slt data (minAnswerOf s) <;> simp [hBool] at hLo ⊢

  have hAfterDataLo := hBase
  rw [hDataLo] at hAfterDataLo
  simp [Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run] at hAfterDataLo

  have hDataHi : sgt data (maxAnswerOf s) = false := by
    by_cases hHi : sgt data (maxAnswerOf s) = true
    · have hBranch := hAfterDataLo
      rw [hHi] at hBranch
      simp [Verity.bind, Bind.bind, Verity.pure, Pure.pure, Verity.require, Contract.run] at hBranch
    · cases hBool : sgt data (maxAnswerOf s) <;> simp [hBool] at hHi ⊢

  have hAfterDataHi := hAfterDataLo
  rw [hDataHi] at hAfterDataHi
  simp [Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run] at hAfterDataHi

  have hGrowthLo : slt growthApr (minGrowthAprOf s) = false := by
    by_cases hLo : slt growthApr (minGrowthAprOf s) = true
    · have hBranch := hAfterDataHi
      rw [hLo] at hBranch
      simp [Verity.bind, Bind.bind, Verity.pure, Pure.pure, Verity.require, Contract.run] at hBranch
    · cases hBool : slt growthApr (minGrowthAprOf s) <;> simp [hBool] at hLo ⊢

  have hAfterGrowthLo := hAfterDataHi
  rw [hGrowthLo] at hAfterGrowthLo
  simp [Verity.bind, Bind.bind, Verity.pure, Pure.pure, Contract.run] at hAfterGrowthLo

  have hGrowthHi : sgt growthApr (maxGrowthAprOf s) = false := by
    by_cases hHi : sgt growthApr (maxGrowthAprOf s) = true
    · have hBranch := hAfterGrowthLo
      rw [hHi] at hBranch
      simp [Verity.bind, Bind.bind, Verity.pure, Pure.pure, Verity.require, Contract.run] at hBranch
    · cases hBool : sgt growthApr (maxGrowthAprOf s) <;> simp [hBool] at hHi ⊢

  have hDataTsLt : dataTimestamp < blockTimestamp := by
    by_cases hLt : dataTimestamp < blockTimestamp
    · exact hLt
    · have hBranch := hAfterGrowthLo
      rw [hGrowthHi] at hBranch
      have hLtVal : ¬ dataTimestamp.val < blockTimestamp.val := by
        simpa using hLt
      have hCondFalse : decide (dataTimestamp.val < blockTimestamp.val) = false := by
        simp [hLtVal]
      simp [hCondFalse, Verity.bind, Bind.bind, Verity.pure, Pure.pure, Verity.require, Contract.run] at hBranch

  unfold answerInRange aprInRange submittedTimestampBeforeCurrentTime
  exact ⟨⟨hDataLo, hDataHi⟩, ⟨⟨hGrowthLo, hGrowthHi⟩, hDataTsLt⟩⟩

private theorem setRoundDataSafe_success_implies_safeInputsOk
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hAccepted : safeAccepted data dataTimestamp growthApr blockTimestamp s) :
    safeInputsOk data dataTimestamp growthApr blockTimestamp s := by
  have hRun := hAccepted
  unfold safeAccepted safeCallResult at hRun
  rw [setRoundDataSafe_eq_with_tail data dataTimestamp growthApr blockTimestamp] at hRun
  have hOnlyUpEval :
      (getStorage CustomFeedGrowthSafe.onlyUp).run s =
        ContractResult.success (onlyUpWordOf s) s := by
    simp [onlyUpWordOf, onlyUpSlot, getStorage, Contract.run]
  have hLastUpdatedEval :
      (CustomFeedGrowthSafe.lastTimestamp.run s) =
        ContractResult.success (lastTimestampOf s) s :=
    lastTimestamp_eval s
  unfold setRoundDataSafeWithTail at hRun
  simp only [Bind.bind] at hRun
  rw [bind_run_success_same_state _ _ _ _ hOnlyUpEval] at hRun
  rw [bind_run_success_same_state _ _ _ _ hLastUpdatedEval] at hRun
  have hHist :=
    setRoundDataSafeHistoryTail_success_implies data dataTimestamp growthApr blockTimestamp s
      (fun _ => CustomFeedGrowthSafe.setRoundData data dataTimestamp growthApr blockTimestamp)
      hRun
  have hInnerInputs :=
    setRoundData_success_implies_inputs data dataTimestamp growthApr blockTimestamp s
      hHist.2.2.2.2.2
  have hTimeGapSpec : respectsTimeGap blockTimestamp s := by
    unfold respectsTimeGap
    have hTimeOrderNat : (lastTimestampOf s : Nat) ≤ (blockTimestamp : Nat) := by
      simpa using hHist.2.2.1
    have hGapNat : ((sub blockTimestamp (lastTimestampOf s) : Uint256) : Nat) > 3600 := by
      simpa using hHist.2.2.2.1
    rw [Verity.EVM.Uint256.sub_eq_of_le hTimeOrderNat] at hGapNat
    simpa using hGapNat
  exact
    ⟨hHist.1, (by
        unfold onlyUpAprNonnegative
        exact hHist.2.1),
      hHist.2.2.1, hTimeGapSpec, hHist.2.2.2.2.1, hInnerInputs.2.2, hInnerInputs.1,
      hInnerInputs.2.1⟩

theorem setRoundDataSafe_rejects_outside_guardrails
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState) :
    setRoundDataSafe_rejects_outside_guardrails_spec
      data dataTimestamp growthApr blockTimestamp s := by
  unfold setRoundDataSafe_rejects_outside_guardrails_spec
  intro hNotSafe
  cases setRoundDataSafe_accepted_or_rejected data dataTimestamp growthApr blockTimestamp s with
  | inl hAccepted =>
      have hSafe :=
        setRoundDataSafe_success_implies_safeInputsOk
          data dataTimestamp growthApr blockTimestamp s hAccepted
      exact False.elim (hNotSafe hSafe)
  | inr hRejected =>
      exact hRejected

private theorem setRoundDataSafe_projected_writes_of_safe_inputs
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hSafeInputs : safeInputsOk data dataTimestamp growthApr blockTimestamp s)
    (storageSlot mapSlot : Nat) (k : Uint256) :
    let s' := ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd
    s'.storage storageSlot = writeStorageAfterRound s storageSlot ∧
      s'.storageMapUint mapSlot k = writeMapUintAfterRound data dataTimestamp growthApr blockTimestamp s mapSlot k := by
  rcases hSafeInputs with
    ⟨hHistoryChecks, hOnlyUpAprCond, hTimeOrder, hTimeGapNat, hStarted, hDataTsLt, hAnswerRange,
      hAprRange⟩
  have hDataLo : slt data (minAnswerOf s) = false := hAnswerRange.1
  have hDataHi : sgt data (maxAnswerOf s) = false := hAnswerRange.2
  have hGrowthLo : slt growthApr (minGrowthAprOf s) = false := hAprRange.1
  have hGrowthHi : sgt growthApr (maxGrowthAprOf s) = false := hAprRange.2
  have hTimeOrderNat : (lastTimestampOf s : Nat) ≤ (blockTimestamp : Nat) := by
    simpa using hTimeOrder
  have hTimeGap :
      sub blockTimestamp (lastTimestampOf s) > 3600 := by
    have hGapNat :
        ((blockTimestamp : Nat) - (lastTimestampOf s : Nat)) > 3600 := by
      simpa [respectsTimeGap] using hTimeGapNat
    have hGapVal :
        ((sub blockTimestamp (lastTimestampOf s) : Uint256) : Nat) > 3600 := by
      change (((blockTimestamp - lastTimestampOf s : Uint256) : Nat) > 3600)
      rw [Verity.Core.Uint256.sub_eq_of_le hTimeOrderNat]
      exact hGapNat
    simpa using hGapVal
  have hPrevStarted :
      lastTimestampOf s != 0 → lastStartedAtOf s <= blockTimestamp := by
    intro _hLastUpdated
    have hPrevStartedNat : (lastStartedAtOf s : Nat) < (blockTimestamp : Nat) := by
      exact Nat.lt_trans (by simpa [advancesStartedAt] using hStarted)
        (by simpa [submittedTimestampBeforeCurrentTime] using hDataTsLt)
    exact Nat.le_of_lt hPrevStartedNat
  have hDataTsLe :
      lastTimestampOf s != 0 → dataTimestamp <= blockTimestamp := by
    intro _hLastUpdated
    exact Nat.le_of_lt (by simpa [submittedTimestampBeforeCurrentTime] using hDataTsLt)
  have hOnlyUpApr :
      onlyUpWordOf s != 0 → slt growthApr 0 = false := by
    intro hOnlyUpNZ
    exact hOnlyUpAprCond (by simpa using hOnlyUpNZ)
  by_cases hLastUpdated0 : lastTimestampOf s = 0
  · by_cases hOnlyUp0 : onlyUpWordOf s = 0
    · exact setRoundDataSafe_zero_history_onlyup_off_writes data dataTimestamp growthApr blockTimestamp s
        hLastUpdated0 hOnlyUp0 hTimeOrder hTimeGap hStarted hDataLo hDataHi hGrowthLo hGrowthHi
        hDataTsLt storageSlot mapSlot k
    · exact setRoundDataSafe_zero_history_onlyup_on_writes data dataTimestamp growthApr blockTimestamp s
        hLastUpdated0 hOnlyUp0 (hOnlyUpApr (by simpa using hOnlyUp0)) hTimeOrder hTimeGap hStarted
        hDataLo hDataHi hGrowthLo hGrowthHi hDataTsLt storageSlot mapSlot k
  · have hLastUpdatedNZ : lastTimestampOf s != 0 := by simpa using hLastUpdated0
    have hHistory' := hHistoryChecks hLastUpdatedNZ
    have hDeviationCap :
        deviationOfSafeCall data dataTimestamp growthApr blockTimestamp s <= maxAnswerDeviationOf s :=
      hHistory'.1
    have hLastAnswerNZCond :
        candidateLivePrice data dataTimestamp growthApr blockTimestamp ≠ 0 →
          lastAnswerOf s blockTimestamp != 0 :=
      hHistory'.2.1
    have hOnlyUpDeviationCond :
        candidateLivePrice data dataTimestamp growthApr blockTimestamp ≠ 0 →
          respectsOnlyUp data dataTimestamp growthApr blockTimestamp s :=
      hHistory'.2.2
    by_cases hCandidateZero : candidateLivePrice data dataTimestamp growthApr blockTimestamp = 0
    · by_cases hOnlyUp0 : onlyUpWordOf s = 0
      · exact setRoundDataSafe_candidate_zero_onlyup_off_writes data dataTimestamp growthApr blockTimestamp s
          hLastUpdated0 (hPrevStarted hLastUpdatedNZ) (hDataTsLe hLastUpdatedNZ) hDeviationCap
          hCandidateZero hOnlyUp0 hTimeOrder hTimeGap hStarted hDataLo hDataHi hGrowthLo
          hGrowthHi hDataTsLt storageSlot mapSlot k
      · exact setRoundDataSafe_candidate_zero_onlyup_on_writes data dataTimestamp growthApr blockTimestamp s
          hLastUpdated0 (hPrevStarted hLastUpdatedNZ) (hDataTsLe hLastUpdatedNZ) hDeviationCap
          hCandidateZero hOnlyUp0 (hOnlyUpApr (by simpa using hOnlyUp0)) hTimeOrder hTimeGap
          hStarted hDataLo hDataHi hGrowthLo hGrowthHi hDataTsLt storageSlot mapSlot k
    · have hLastAnswerNZ : lastAnswerOf s blockTimestamp != 0 := hLastAnswerNZCond hCandidateZero
      by_cases hOnlyUp0 : onlyUpWordOf s = 0
      · exact setRoundDataSafe_candidate_nonzero_onlyup_off_writes data dataTimestamp growthApr blockTimestamp s
          hLastUpdated0 (hPrevStarted hLastUpdatedNZ) (hDataTsLe hLastUpdatedNZ) hLastAnswerNZ
          hDeviationCap hCandidateZero hOnlyUp0 hTimeOrder hTimeGap hStarted hDataLo hDataHi
          hGrowthLo hGrowthHi hDataTsLt storageSlot mapSlot k
      · have hOnlyUpDeviation :
            slt (signedDeviationOfSafeCall data dataTimestamp growthApr blockTimestamp s) 0 = false :=
          (hOnlyUpDeviationCond hCandidateZero) (by simpa using hOnlyUp0)
        exact setRoundDataSafe_candidate_nonzero_onlyup_on_writes data dataTimestamp growthApr blockTimestamp s
          hLastUpdated0 (hPrevStarted hLastUpdatedNZ) (hDataTsLe hLastUpdatedNZ) hLastAnswerNZ
          hOnlyUpDeviation hDeviationCap hCandidateZero hOnlyUp0
          (hOnlyUpApr (by simpa using hOnlyUp0)) hTimeOrder hTimeGap hStarted hDataLo hDataHi
          hGrowthLo hGrowthHi hDataTsLt storageSlot mapSlot k

theorem setRoundDataSafe_accepts_and_writes_submitted_round
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState) :
    setRoundDataSafe_accepts_and_writes_submitted_round_spec
      data dataTimestamp growthApr blockTimestamp s := by
  unfold setRoundDataSafe_accepts_and_writes_submitted_round_spec
  dsimp
  intro hSafeInputs
  let s' := ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd
  have hLatestWrites :=
    setRoundDataSafe_projected_writes_of_safe_inputs data dataTimestamp growthApr blockTimestamp s
      hSafeInputs CustomFeedGrowthSafe.latestRound.slot 0 0
  have hAnswerWrites :=
    setRoundDataSafe_projected_writes_of_safe_inputs data dataTimestamp growthApr blockTimestamp s
      hSafeInputs 0 CustomFeedGrowthSafe.roundAnswer.slot (nextRoundIdOf s)
  have hStartedWrites :=
    setRoundDataSafe_projected_writes_of_safe_inputs data dataTimestamp growthApr blockTimestamp s
      hSafeInputs 0 CustomFeedGrowthSafe.roundStartedAt.slot (nextRoundIdOf s)
  have hUpdatedWrites :=
    setRoundDataSafe_projected_writes_of_safe_inputs data dataTimestamp growthApr blockTimestamp s
      hSafeInputs 0 CustomFeedGrowthSafe.roundUpdatedAt.slot (nextRoundIdOf s)
  have hGrowthWrites :=
    setRoundDataSafe_projected_writes_of_safe_inputs data dataTimestamp growthApr blockTimestamp s
      hSafeInputs 0 CustomFeedGrowthSafe.roundGrowthApr.slot (nextRoundIdOf s)
  have hWrites :
      writesSubmittedRound data dataTimestamp growthApr blockTimestamp s
        ((safeCallResult data dataTimestamp growthApr blockTimestamp s).snd) := by
    unfold writesSubmittedRound
    unfold safeCallResult
    have hLatest :
        latestRoundOf
            (((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd) =
          nextRoundIdOf s := by
      simpa [writeStorageAfterRound, nextRoundIdOf, latestRoundOf] using hLatestWrites.1
    have hAnswer :
        roundAnswerOf
            (((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd)
            (nextRoundIdOf s) = data := by
      simpa [writeMapUintAfterRound, nextRoundIdOf, roundAnswerOf, roundAnswerSlot, roundStartedAtSlot,
        roundUpdatedAtSlot, roundGrowthAprSlot] using hAnswerWrites.2
    have hStartedAt :
        roundStartedAtOf
            (((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd)
            (nextRoundIdOf s) = dataTimestamp := by
      simpa [writeMapUintAfterRound, nextRoundIdOf, roundStartedAtOf, roundAnswerSlot, roundStartedAtSlot,
        roundUpdatedAtSlot, roundGrowthAprSlot] using hStartedWrites.2
    have hUpdated :
        roundUpdatedAtOf
            (((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd)
            (nextRoundIdOf s) = blockTimestamp := by
      simpa [writeMapUintAfterRound, nextRoundIdOf, roundUpdatedAtOf, roundAnswerSlot, roundStartedAtSlot,
        roundUpdatedAtSlot, roundGrowthAprSlot] using hUpdatedWrites.2
    have hGrowth :
        roundGrowthAprOf
            (((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd)
            (nextRoundIdOf s) = growthApr := by
      simpa [writeMapUintAfterRound, nextRoundIdOf, roundGrowthAprOf, roundAnswerSlot, roundStartedAtSlot,
        roundUpdatedAtSlot, roundGrowthAprSlot] using hGrowthWrites.2
    refine ⟨hLatest, ?_, ?_, ?_, ?_⟩
    · rw [hLatest]
      exact hAnswer
    · rw [hLatest]
      exact hStartedAt
    · rw [hLatest]
      exact hUpdated
    · rw [hLatest]
      exact hGrowth
  have hAccepted : safeAccepted data dataTimestamp growthApr blockTimestamp s := by
    have hOutcome := setRoundDataSafe_accepted_or_rejected data dataTimestamp growthApr blockTimestamp s
    cases hOutcome with
    | inl hAccepted =>
        exact hAccepted
    | inr hRejected =>
        have hSnd : (safeCallResult data dataTimestamp growthApr blockTimestamp s).snd = s :=
          safeRejected_snd_eq data dataTimestamp growthApr blockTimestamp s hRejected
        have hWritesAtStart : writesSubmittedRound data dataTimestamp growthApr blockTimestamp s s := by
          simpa [hSnd] using hWrites
        exact False.elim (latestRound_ne_nextRoundId s hWritesAtStart.1)
  exact ⟨hAccepted, hWrites⟩

theorem setRoundDataSafe_full_correctness
    (data dataTimestamp growthApr blockTimestamp : Uint256) (s : ContractState)
    (hLatest : latestRoundOf s >= 1)
    (hLastUpdated : lastTimestampOf s != 0)
    (hPrevStarted : lastTimestampOf s != 0 → lastStartedAtOf s <= blockTimestamp)
    (hDataTsLe : lastTimestampOf s != 0 → dataTimestamp <= blockTimestamp)
    (hLastAnswerNZ :
      lastTimestampOf s != 0 → candidateLivePrice data dataTimestamp growthApr blockTimestamp ≠ 0 →
        lastAnswerOf s blockTimestamp != 0)
    (hOnlyUpDeviation :
      lastTimestampOf s != 0 → onlyUpWordOf s != 0 →
        slt (signedDeviationOfSafeCall data dataTimestamp growthApr blockTimestamp s) 0 = false)
    (hDeviationCap :
      lastTimestampOf s != 0 →
        deviationOfSafeCall data dataTimestamp growthApr blockTimestamp s <= maxAnswerDeviationOf s)
    (hOnlyUpApr : onlyUpWordOf s != 0 → slt growthApr 0 = false)
    (hTimeOrder : lastTimestampOf s <= blockTimestamp)
    (hTimeGap : sub blockTimestamp (lastTimestampOf s) > 3600)
    (hStarted : dataTimestamp > lastStartedAtOf s)
    (hDataLo : slt data (minAnswerOf s) = false)
    (hDataHi : sgt data (maxAnswerOf s) = false)
    (hGrowthLo : slt growthApr (minGrowthAprOf s) = false)
    (hGrowthHi : sgt growthApr (maxGrowthAprOf s) = false)
    (hDataTsLt : dataTimestamp < blockTimestamp)
    (hRejectZero : maxAnswerDeviationOf s < HUNDRED_ONE) :
    let s' := ((CustomFeedGrowthSafe.setRoundDataSafe data dataTimestamp growthApr blockTimestamp).run s).snd
    SetRoundDataSafeFullCorrectnessSpec data dataTimestamp growthApr blockTimestamp s s' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact setRoundDataSafe_rejects_zero_price dataTimestamp growthApr blockTimestamp s
      hLatest hLastUpdated hRejectZero
  · exact setRoundDataSafe_deviation_bound data dataTimestamp growthApr blockTimestamp s
      hLatest hLastUpdated (hDeviationCap hLastUpdated)
  · exact setRoundDataSafe_enforces_time_gap data dataTimestamp growthApr blockTimestamp s
      hTimeOrder hTimeGap
  · exact setRoundDataSafe_startedAt_monotonic data dataTimestamp growthApr blockTimestamp s
      hPrevStarted hDataTsLe hLastAnswerNZ hOnlyUpDeviation hDeviationCap hOnlyUpApr
      hTimeOrder hTimeGap hStarted hDataLo hDataHi hGrowthLo hGrowthHi hDataTsLt
  · exact setRoundDataSafe_onlyUp_nonnegative_deviation data dataTimestamp growthApr blockTimestamp s
      hLatest hLastUpdated (hOnlyUpDeviation hLastUpdated)
  · exact setRoundDataSafe_propagates_band_guard data dataTimestamp growthApr blockTimestamp s
      hPrevStarted hDataTsLe hLastAnswerNZ hOnlyUpDeviation hDeviationCap hOnlyUpApr
      hTimeOrder hTimeGap hStarted hDataLo hDataHi hGrowthLo hGrowthHi hDataTsLt

end Benchmark.Cases.Midas.CustomFeedGrowthSafe
