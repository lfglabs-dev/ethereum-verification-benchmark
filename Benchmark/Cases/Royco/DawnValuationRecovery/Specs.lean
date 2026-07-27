import Benchmark.Cases.Royco.DawnValuationRecovery.Contract

namespace Benchmark.Cases.Royco.DawnValuationRecovery

/-!
# Specifications

The headline invariant is the exact ordered liability-recovery waterfall selected
in Phase 1. Inductive NAV conservation, claim-attribution residual, complete loss
booking, and forced-perpetual JT-liability erasure are separate supporting claims.
-/

/-- Raw NAV carried by the synchronized state. Article-facing helper. -/
def totalRawNAV (state : SyncedAccountingState) : Nat :=
  state.stRawNAV + state.jtRawNAV

/-- Effective NAV carried by the synchronized state. Article-facing helper. -/
def totalEffectiveNAV (state : SyncedAccountingState) : Nat :=
  state.stEffectiveNAV + state.jtEffectiveNAV

/-- Effective NAV at the source's line-585 conservation checkpoint, before
    market-state resolution and any explicit JT-liability erasure. -/
def allocationEffectiveNAV (state : AllocationState) : Nat :=
  state.stEffectiveNAV + state.jtEffectiveNAV

/-- The source pre-state already satisfies the same checkpoint invariant. -/
def preStateConserved (s : AccountantState) : Prop :=
  s.lastSTEffectiveNAV + s.lastJTEffectiveNAV = s.lastSTRawNAV + s.lastJTRawNAV

/-- A signed source intermediate fits Solidity `int256`. -/
def fitsInt256 (x : Int) : Prop :=
  -(Int.ofNat (2 ^ 255)) <= x ∧ x <= Int.ofNat INT256_MAX

/-- A signed waterfall delta can also be negated without hitting `int256.min`. -/
def safeNegatableInt256 (x : Int) : Prop :=
  -(Int.ofNat INT256_MAX) <= x ∧ x <= Int.ofNat INT256_MAX

/-- All storage and call values fit their Solidity source widths. -/
def sourceValuesFit (s : AccountantState) (input : SyncInput) : Prop :=
  s.lastSTRawNAV <= INT256_MAX ∧
  s.lastJTRawNAV <= INT256_MAX ∧
  input.stRawNAV <= INT256_MAX ∧
  input.jtRawNAV <= INT256_MAX ∧
  s.lastSTEffectiveNAV <= UINT256_MAX ∧
  s.lastJTEffectiveNAV <= UINT256_MAX ∧
  s.lastSTImpermanentLoss <= UINT256_MAX ∧
  s.lastJTImpermanentLoss <= UINT256_MAX ∧
  s.stNAVDustTolerance <= UINT256_MAX ∧
  s.jtNAVDustTolerance <= UINT256_MAX ∧
  s.stProtocolFeeWAD <= WAD ∧
  s.jtProtocolFeeWAD <= WAD ∧
  s.yieldShareProtocolFeeWAD <= WAD ∧
  s.lastDistributionTimestamp <= UINT32_MAX ∧
  input.timestamp <= UINT256_MAX ∧
  input.twJTYieldShareAccruedWAD <= UINT192_MAX ∧
  input.instantaneousJTYieldShareWAD <= UINT256_MAX ∧
  s.fixedTermEndTimestamp <= UINT32_MAX ∧
  s.fixedTermDurationSeconds <= UINT24_MAX ∧
  s.betaWAD <= UINT96_MAX ∧
  s.coverageWAD <= UINT64_MAX ∧
  s.stProtocolFeeWAD <= UINT64_MAX ∧
  s.jtProtocolFeeWAD <= UINT64_MAX ∧
  s.yieldShareProtocolFeeWAD <= UINT64_MAX ∧
  s.liquidationUtilizationWAD <= UINT256_MAX

/-- Residual ST gain after both liability-recovery layers, before the yield split. -/
def residualSTGainAfterRecovery (afterJT : AllocationState) (deltaST : Int) : Nat :=
  if deltaST > 0 then
    let gain := deltaST.natAbs
    let afterSTIL := gain - min gain afterJT.stImpermanentLoss
    afterSTIL - min afterSTIL afterJT.jtImpermanentLoss
  else
    0

/-- Every checked arithmetic operation in the JT leg is safe in source order. -/
def jtLegArithmeticSafe (s : AccountantState) (deltaJT : Int) : Prop :=
  let dust := s.stNAVDustTolerance + s.jtNAVDustTolerance
  if deltaJT < 0 then
    let loss := deltaJT.natAbs
    let absorbedByJT := min loss s.lastJTEffectiveNAV
    let uncovered := loss - absorbedByJT
    uncovered <= s.lastSTEffectiveNAV ∧
    s.lastSTImpermanentLoss + uncovered <= UINT256_MAX
  else if deltaJT > 0 then
    let gain := deltaJT.natAbs
    let stRecovery := min gain s.lastSTImpermanentLoss
    let residualJTGain := gain - stRecovery
    s.lastSTEffectiveNAV + stRecovery <= UINT256_MAX ∧
    s.lastJTEffectiveNAV + residualJTGain <= UINT256_MAX ∧
    (residualJTGain > dust →
      mulDivFloor residualJTGain s.jtProtocolFeeWAD WAD <= UINT256_MAX)
  else
    True

/-- Every checked arithmetic operation in the ST leg is safe in source order. -/
def stLegArithmeticSafe
    (s : AccountantState) (input : SyncInput)
    (afterJT : AllocationState) (deltaST : Int) : Prop :=
  let dust := s.stNAVDustTolerance + s.jtNAVDustTolerance
  if deltaST < 0 then
    let loss := deltaST.natAbs
    let coverage := min loss afterJT.jtEffectiveNAV
    let uncovered := loss - coverage
    let recomputedJTNetGain := saturatingSub afterJT.jtNetGain coverage
    uncovered <= afterJT.stEffectiveNAV ∧
    afterJT.jtImpermanentLoss + coverage <= UINT256_MAX ∧
    afterJT.stImpermanentLoss + uncovered <= UINT256_MAX ∧
    (afterJT.jtProtocolFeeAccrued ≠ 0 →
      recomputedJTNetGain > dust →
      mulDivFloor recomputedJTNetGain s.jtProtocolFeeWAD WAD <= UINT256_MAX)
  else if deltaST > 0 then
    let gain := deltaST.natAbs
    let stRecovery := min gain afterJT.stImpermanentLoss
    let afterSTRecovery := gain - stRecovery
    let jtRecovery := min afterSTRecovery afterJT.jtImpermanentLoss
    let residualSTYield := afterSTRecovery - jtRecovery
    let yieldShare := computeYieldShare s input residualSTYield
    let stResidualAfterYieldShare := residualSTYield - yieldShare
    yieldShare <= residualSTYield ∧
    afterJT.stEffectiveNAV + stRecovery <= UINT256_MAX ∧
    afterJT.stEffectiveNAV + stRecovery + stResidualAfterYieldShare <= UINT256_MAX ∧
    afterJT.jtEffectiveNAV + jtRecovery <= UINT256_MAX ∧
    afterJT.jtEffectiveNAV + jtRecovery + yieldShare <= UINT256_MAX ∧
    (residualSTYield > dust →
      afterJT.jtProtocolFeeAccrued +
        mulDivFloor yieldShare s.yieldShareProtocolFeeWAD WAD <= UINT256_MAX) ∧
    (residualSTYield > dust →
      mulDivFloor stResidualAfterYieldShare s.stProtocolFeeWAD WAD <= UINT256_MAX)
  else
    True

/-- The exact checked operations used by `UtilsLib.computeUtilization`. -/
def utilizationArithmeticSafe
    (s : AccountantState) (input : SyncInput) (jtEffectiveNAV : Nat) : Prop :=
  let coveredJTExposure := mulDivCeil input.jtRawNAV s.betaWAD WAD
  let totalCoveredExposure := input.stRawNAV + coveredJTExposure
  coveredJTExposure <= UINT256_MAX ∧
  totalCoveredExposure <= UINT256_MAX ∧
  (totalCoveredExposure ≠ 0 → jtEffectiveNAV ≠ 0 →
    mulDivCeil s.coverageWAD totalCoveredExposure jtEffectiveNAV <= UINT256_MAX)

/-- Checked signed operations at source lines 437-451, in Solidity association
order, plus the full-precision attribution quotient result bounds. -/
def signedAttributionArithmeticSafe
    (s : AccountantState) (deltas : EffectiveDeltas) : Prop :=
  let stAttributedSum :=
    deltas.deltaSTClaimOnSTRawNAV + deltas.deltaSTClaimOnJTRawNAV
  let rawDeltaSum := deltas.deltaSTRawNAV + deltas.deltaJTRawNAV
  fitsInt256 stAttributedSum ∧
  fitsInt256 rawDeltaSum ∧
  fitsInt256 (rawDeltaSum - deltas.deltaSTEffectiveNAV) ∧
  safeNegatableInt256 deltas.deltaSTEffectiveNAV ∧
  safeNegatableInt256 deltas.deltaJTEffectiveNAV ∧
  deltas.stClaimOnJTRawNAV <= s.lastJTRawNAV ∧
  (s.lastSTRawNAV ≠ 0 →
    deltas.deltaSTRawNAV.natAbs * deltas.stClaimOnSTRawNAV /
      s.lastSTRawNAV <= UINT256_MAX) ∧
  (s.lastJTRawNAV ≠ 0 →
    deltas.deltaJTRawNAV.natAbs * deltas.stClaimOnJTRawNAV /
      s.lastJTRawNAV <= UINT256_MAX)

/-- Explicit successful-path bounds corresponding to every Solidity checked
arithmetic operation and the accumulator invariants used by this slice.

These assumptions do not contain any post-state recovery identity or conservation
conclusion. They only describe a non-reverting source execution plus the inductive
pre-state conservation hypothesis. -/
def successfulSyncAssumptions (s : AccountantState) (input : SyncInput) : Prop :=
  let deltas := computeEffectiveDeltas s input
  let afterJT := applyJTEffectiveDelta s deltas.deltaJTEffectiveNAV
  let allocated := applySTEffectiveDelta s input afterJT deltas.deltaSTEffectiveNAV
  let residualSTGain := residualSTGainAfterRecovery afterJT deltas.deltaSTEffectiveNAV
  let utilization :=
    computeUtilization input.stRawNAV input.jtRawNAV s.betaWAD s.coverageWAD
      allocated.jtEffectiveNAV
  sourceValuesFit s input ∧
  preStateConserved s ∧
  (residualSTGain > 0 → input.timestamp >= s.lastDistributionTimestamp) ∧
  deltas.jtClaimOnSTRawNAV <= s.lastSTRawNAV ∧
  signedAttributionArithmeticSafe s deltas ∧
  s.lastSTRawNAV + s.lastJTRawNAV <= UINT256_MAX ∧
  input.stRawNAV + input.jtRawNAV <= UINT256_MAX ∧
  s.stNAVDustTolerance + s.jtNAVDustTolerance <= UINT256_MAX ∧
  jtLegArithmeticSafe s deltas.deltaJTEffectiveNAV ∧
  afterJT.stEffectiveNAV <= UINT256_MAX ∧
  afterJT.jtEffectiveNAV <= UINT256_MAX ∧
  afterJT.stImpermanentLoss <= UINT256_MAX ∧
  afterJT.jtImpermanentLoss <= UINT256_MAX ∧
  afterJT.jtProtocolFeeAccrued <= UINT256_MAX ∧
  stLegArithmeticSafe s input afterJT deltas.deltaSTEffectiveNAV ∧
  (residualSTGain > 0 → input.timestamp > s.lastDistributionTimestamp →
    (input.timestamp - s.lastDistributionTimestamp) * WAD <= UINT256_MAX) ∧
  (residualSTGain > 0 → input.timestamp > s.lastDistributionTimestamp →
    input.twJTYieldShareAccruedWAD <=
      (input.timestamp - s.lastDistributionTimestamp) * WAD) ∧
  allocated.stEffectiveNAV <= UINT256_MAX ∧
  allocated.jtEffectiveNAV <= UINT256_MAX ∧
  allocated.stImpermanentLoss <= UINT256_MAX ∧
  allocated.jtImpermanentLoss <= UINT256_MAX ∧
  allocated.stProtocolFeeAccrued <= UINT256_MAX ∧
  allocated.jtProtocolFeeAccrued <= UINT256_MAX ∧
  allocationEffectiveNAV allocated <= UINT256_MAX ∧
  utilizationArithmeticSafe s input allocated.jtEffectiveNAV ∧
  utilization <= UINT256_MAX ∧
  (forcedPerpetual s input allocated utilization = false →
    allocated.jtImpermanentLoss > s.stNAVDustTolerance + s.jtNAVDustTolerance →
    s.lastMarketState = .perpetual →
    input.timestamp + s.fixedTermDurationSeconds <= UINT256_MAX)

/-- **Supporting invariant: valuation is neither created nor destroyed.**

If the previous checkpoint was conserved and all Solidity checked arithmetic
succeeds, synchronization preserves total effective NAV exactly equal to the
new total raw NAV. The equality is stated both at the source's explicit
line-585 checkpoint and on the final returned state. -/
def preview_sync_preserves_nav_conservation_spec
    (s : AccountantState) (input : SyncInput) : Prop :=
  successfulSyncAssumptions s input →
    let result := previewSyncTrancheAccounting s input
    allocationEffectiveNAV result.allocationState = totalRawNAV result.state ∧
    totalEffectiveNAV result.state = totalRawNAV result.state

/-- The JT effective delta is defined as the signed residual after the ST claim
    attribution. Therefore floor-rounding dust cannot disappear from aggregate
    valuation. -/
def attribution_residual_absorbed_by_junior_spec
    (s : AccountantState) (input : SyncInput) : Prop :=
  let deltas := computeEffectiveDeltas s input
  deltas.deltaSTEffectiveNAV + deltas.deltaJTEffectiveNAV =
    deltas.deltaSTRawNAV + deltas.deltaJTRawNAV

/-- **Headline invariant: exact ordered recovery waterfall.**

Every positive JT effective delta is partitioned exactly into ST-IL recovery and
residual JT gain. Every positive ST effective delta is partitioned exactly into
ST-IL recovery, JT-coverage-IL recovery, and residual fresh yield. A nonzero
lower-priority amount implies that every higher-priority liability is zero. -/
def recovery_waterfall_orders_liabilities_spec
    (s : AccountantState) (input : SyncInput) : Prop :=
  successfulSyncAssumptions s input →
    let result := previewSyncTrancheAccounting s input
    let deltas := result.effectiveDeltas
    let trace := result.recoveryTrace
    let jtGain :=
      if deltas.deltaJTEffectiveNAV > 0 then deltas.deltaJTEffectiveNAV.natAbs else 0
    let stGain :=
      if deltas.deltaSTEffectiveNAV > 0 then deltas.deltaSTEffectiveNAV.natAbs else 0
    trace.stRecoveryFromJT = min jtGain s.lastSTImpermanentLoss ∧
    trace.stRecoveryFromJT + trace.residualJTGain = jtGain ∧
    trace.stRecoveryFromST = min stGain result.afterJT.stImpermanentLoss ∧
    trace.jtRecoveryFromST =
      min (stGain - trace.stRecoveryFromST) result.afterJT.jtImpermanentLoss ∧
    trace.stRecoveryFromST + trace.jtRecoveryFromST + trace.residualSTYield = stGain ∧
    (trace.residualJTGain > 0 → result.afterJT.stImpermanentLoss = 0) ∧
    (trace.jtRecoveryFromST > 0 → result.allocationState.stImpermanentLoss = 0) ∧
    (trace.residualSTYield > 0 →
      result.allocationState.stImpermanentLoss = 0 ∧
      result.allocationState.jtImpermanentLoss = 0)

/-- **The market-state erasure is explicit, not hidden in the waterfall.**

When the source's forced-perpetual disjunction holds, the returned JT coverage
liability is zero and the exact pre-erasure amount is preserved in the trace.
Effective NAV is unchanged by this bookkeeping transition. -/
def forced_perpetual_erasure_is_explicit_spec
    (s : AccountantState) (input : SyncInput) : Prop :=
  let result := previewSyncTrancheAccounting s input
  forcedPerpetual s input result.allocationState result.state.utilizationWAD = true →
    result.state.marketState = MarketState.perpetual ∧
    result.state.jtImpermanentLoss = 0 ∧
    result.jtImpermanentLossErased = result.allocationState.jtImpermanentLoss ∧
    result.state.stEffectiveNAV = result.allocationState.stEffectiveNAV ∧
    result.state.jtEffectiveNAV = result.allocationState.jtEffectiveNAV

/-- Loss-side trace used by reviewers to check the complete waterfall, even
    though the public claim focuses on recovery. -/
def losses_are_booked_to_the_correct_liability_spec
    (s : AccountantState) (input : SyncInput) : Prop :=
  successfulSyncAssumptions s input →
  let deltas := computeEffectiveDeltas s input
  let afterJT := applyJTEffectiveDelta s deltas.deltaJTEffectiveNAV
  let allocated := applySTEffectiveDelta s input afterJT deltas.deltaSTEffectiveNAV
  let jtLossTrace :=
    if deltas.deltaJTEffectiveNAV < 0 then
      let loss := deltas.deltaJTEffectiveNAV.natAbs
      let absorbedByJT := min loss s.lastJTEffectiveNAV
      let uncovered := loss - absorbedByJT
      afterJT.jtEffectiveNAV = s.lastJTEffectiveNAV - absorbedByJT ∧
      afterJT.stEffectiveNAV = s.lastSTEffectiveNAV - uncovered ∧
      afterJT.stImpermanentLoss = s.lastSTImpermanentLoss + uncovered
    else
      True
  let stLossTrace :=
    if deltas.deltaSTEffectiveNAV < 0 then
      let loss := deltas.deltaSTEffectiveNAV.natAbs
      let coverage := min loss afterJT.jtEffectiveNAV
      let uncovered := loss - coverage
      allocated.jtEffectiveNAV = afterJT.jtEffectiveNAV - coverage ∧
      allocated.jtImpermanentLoss = afterJT.jtImpermanentLoss + coverage ∧
      allocated.stEffectiveNAV = afterJT.stEffectiveNAV - uncovered ∧
      allocated.stImpermanentLoss = afterJT.stImpermanentLoss + uncovered
    else
      True
  jtLossTrace ∧ stLossTrace

/-- Regression state for the signed-overflow boundary identified during review. -/
def signedOverflowBoundaryState : AccountantState where
  lastMarketState := .perpetual
  lastSTRawNAV := 0
  lastJTRawNAV := 0
  lastSTEffectiveNAV := 0
  lastJTEffectiveNAV := 0
  lastSTImpermanentLoss := 0
  lastJTImpermanentLoss := 0
  stNAVDustTolerance := 0
  jtNAVDustTolerance := 0
  stProtocolFeeWAD := 0
  jtProtocolFeeWAD := 0
  yieldShareProtocolFeeWAD := 0
  lastDistributionTimestamp := 0
  fixedTermEndTimestamp := 0
  fixedTermDurationSeconds := 0
  betaWAD := 0
  coverageWAD := 0
  liquidationUtilizationWAD := 0

def signedOverflowBoundaryInput : SyncInput where
  stRawNAV := INT256_MAX
  jtRawNAV := INT256_MAX
  twJTYieldShareAccruedWAD := 0
  timestamp := 0
  instantaneousJTYieldShareWAD := 0

/-- The unbounded-Int counterexample is not admitted as a successful Solidity path. -/
def signed_delta_overflow_boundary_rejected_spec : Prop :=
  ¬ successfulSyncAssumptions signedOverflowBoundaryState signedOverflowBoundaryInput

end Benchmark.Cases.Royco.DawnValuationRecovery
