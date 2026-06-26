import Benchmark.Cases.T3tris.HwmPerformanceFee.Contract

namespace Benchmark.Cases.T3tris.HwmPerformanceFee

/--
Successful-path assumptions for the arithmetic slice.

`unclaimedSharesFee <= totalSupply` corresponds to Solidity `rawSub` not
reverting when net supply is computed. `performanceFeeWad <= WAD` is enforced
by `_validateFeeWad`. `ppsHighWaterMark >= WAD` is the already-proved Cyfrin
structural invariant VS-VA-32 and is kept as a bridge assumption here.
-/
def successfulPeriodAssumptions
    (gross : GrossTvlData)
    (params : PeriodFeesParams)
    (_managementFee : ManagementFeeModel := noManagementFee) : Prop :=
  params.unclaimedSharesFee <= gross.totalSupply /\
  params.performanceFeeWad <= WAD /\
  params.ppsHighWaterMark >= WAD

/--
Single-step HWM trigger property:
if the pre-performance-fee PPS does not exceed the cached HWM, no performance
fee assets or shares are charged.
-/
def no_performance_fee_when_pre_pps_le_hwm_spec
    (gross : GrossTvlData)
    (params : PeriodFeesParams)
    (managementFee : ManagementFeeModel := noManagementFee) : Prop :=
  let result := computeLastPeriodFeesAndUpdateResult gross params managementFee
  result.lastPeriodData.prePerformancePps <= params.ppsHighWaterMark ->
    result.lastPeriodData.performanceFeeAssets = 0 /\
    result.lastPeriodData.performanceFeeShares = 0

/--
The profitable branch must compute PnL against the cached fee-accounted HWM,
not against an earlier lower HWM.
-/
def profit_pnl_uses_cached_hwm_spec
    (gross : GrossTvlData)
    (params : PeriodFeesParams)
    (managementFee : ManagementFeeModel := noManagementFee) : Prop :=
  let result := computeLastPeriodFeesAndUpdateResult gross params managementFee
  result.lastPeriodData.prePerformancePps > params.ppsHighWaterMark ->
    result.lastPeriodData.pnl =
      (result.lastPeriodData.prePerformancePps - params.ppsHighWaterMark) *
        result.lastPeriodData.oldTotalNetSupply / WAD

/--
Multi-step no-double-charge trajectory:

1. A profitable step stores a new fee-accounted HWM.
2. A later loss/recovery step with pre-fee PPS at or below that HWM charges no
   performance fee and does not move HWM.
3. A second recovery step still at or below that same HWM also charges no
   performance fee and leaves HWM unchanged.

This is the economic property missing from the Cyfrin suite; monotonic HWM alone
does not relate the fee base to loss-then-recovery trajectories.
-/
def gain_loss_recovery_no_double_charge_spec
    (s0 : FeeState)
    (gainAssets lossAssets recoveryAssets : Nat)
    (gainManagementFee : ManagementFeeModel := noManagementFee)
    (lossManagementFee : ManagementFeeModel := noManagementFee)
    (recoveryManagementFee : ManagementFeeModel := noManagementFee) : Prop :=
  let step1 := periodStepNoReanchor s0 gainAssets gainManagementFee
  let s1 := step1.fst
  let r1 := step1.snd
  let step2 := periodStepNoReanchor s1 lossAssets lossManagementFee
  let s2 := step2.fst
  let r2 := step2.snd
  let step3 := periodStepNoReanchor s2 recoveryAssets recoveryManagementFee
  let s3 := step3.fst
  let r3 := step3.snd
  r1.lastPeriodData.prePerformancePps > s0.ppsHighWaterMark ->
  r1.lastPeriodData.performanceFeeShares > 0 ->
  r2.lastPeriodData.prePerformancePps <= s1.ppsHighWaterMark ->
  r3.lastPeriodData.prePerformancePps <= s1.ppsHighWaterMark ->
    r2.lastPeriodData.performanceFeeAssets = 0 /\
    r2.lastPeriodData.performanceFeeShares = 0 /\
    s2.ppsHighWaterMark = s1.ppsHighWaterMark /\
    r3.lastPeriodData.performanceFeeAssets = 0 /\
    r3.lastPeriodData.performanceFeeShares = 0 /\
    s3.ppsHighWaterMark = s1.ppsHighWaterMark

/--
After a loss/recovery sequence, the next profitable step must use the latest
stored fee-accounted HWM as the fee base. A proof of this spec rules out using
the pre-profit HWM again after recovery.
-/
def recovery_then_new_high_uses_stored_hwm_spec
    (s0 : FeeState)
    (gainAssets lossAssets recoveryAssets newHighAssets : Nat)
    (gainManagementFee : ManagementFeeModel := noManagementFee)
    (lossManagementFee : ManagementFeeModel := noManagementFee)
    (recoveryManagementFee : ManagementFeeModel := noManagementFee)
    (newHighManagementFee : ManagementFeeModel := noManagementFee) : Prop :=
  let step1 := periodStepNoReanchor s0 gainAssets gainManagementFee
  let s1 := step1.fst
  let step2 := periodStepNoReanchor s1 lossAssets lossManagementFee
  let s2 := step2.fst
  let step3 := periodStepNoReanchor s2 recoveryAssets recoveryManagementFee
  let s3 := step3.fst
  let step4 := periodStepNoReanchor s3 newHighAssets newHighManagementFee
  let r4 := step4.snd
  s3.ppsHighWaterMark = s1.ppsHighWaterMark ->
  r4.lastPeriodData.prePerformancePps > s3.ppsHighWaterMark ->
    r4.lastPeriodData.pnl =
      (r4.lastPeriodData.prePerformancePps - s1.ppsHighWaterMark) *
        r4.lastPeriodData.oldTotalNetSupply / WAD

end Benchmark.Cases.T3tris.HwmPerformanceFee
