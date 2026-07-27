import Mathlib.Data.Int.Basic

/-!
# Royco Dawn valuation-recovery waterfall

Source-faithful arithmetic model of `RoycoAccountant._previewSyncTrancheAccounting`.

Upstream: lfglabs-dev/royco-dawn
Commit:   5fd7c9922b7bd1d9c860ce4ce39c339d28798cb2
Files:    src/accountant/RoycoAccountant.sol
          src/libraries/Units.sol
          src/libraries/UtilsLib.sol

Selected functions:
- `_previewSyncTrancheAccounting` (`RoycoAccountant.sol:405-656`)
- `_attributeDeltaToClaimOnRawNAV` (`RoycoAccountant.sol:843-860`)
- `UnitsMathLib.computeNAVDelta` (`Units.sol:29-32`)
- `UtilsLib.computeUtilization` (`UtilsLib.sol:32-51`)

## Simplifications

1. NAV values are represented by `Nat` and signed deltas by `Int`, rather than
   `uint256` and `int256`. Every source-order signed/unsigned checked operation is
   guarded by `Specs.successfulSyncAssumptions`; the explicit `uint32` timestamp
   cast is modeled by truncation. Current Verity supports explicit checked word
   operations. The relevant gaps are automatic Solidity checked-obligation
   generation (#1993) and first-class narrow integers (#2086).
2. The view function's storage is an immutable `AccountantState` input and its
   memory return value is a Lean structure. No source mutation is omitted:
   `_previewSyncTrancheAccounting` only reads storage and builds a memory result.
3. `IYDM.previewJTYieldShare` is an external read. Its return value is supplied
   as `instantaneousJTYieldShareWAD`; the source's WAD cap, elapsed-time branch,
   floor rounding, and yield allocation are modeled exactly. Supplying the read
   result and explicit view storage are deliberate slice boundaries, not missing
   Verity capabilities.
4. `_twJTYieldShareAccruedWAD` is supplied exactly as it is to the Solidity
   function. Accumulator construction in `_previewJTYieldShareAccrual` is outside
   this function boundary; its source invariant is exposed as the explicit
   accrued-share bound in `successfulSyncAssumptions`.
5. Events and custom revert payloads are outside this view function's returned
   accounting state. Reverting arithmetic paths are excluded only through the
   named successful-path assumptions, not silently saturated in a theorem.
6. `mulDiv` is defined over unbounded naturals with the same floor/ceil result.
   Current Verity has Lean-level 512-bit mulDiv helpers; the direct mathematical
   formula is a chosen abstraction, with every result-fit bound explicit.

No waterfall branch is removed. Claim attribution, JT loss/gain, ST loss/gain,
ST-IL recovery, JT-coverage-IL recovery, yield splitting, fee recomputation,
NAV conservation boundary, market-state transition, and explicit JT-IL erasure
are all represented in source order.
-/

namespace Benchmark.Cases.Royco.DawnValuationRecovery

def WAD : Nat := 10 ^ 18

def UINT24_MAX : Nat := 2 ^ 24 - 1

def UINT32_MAX : Nat := 2 ^ 32 - 1

def UINT64_MAX : Nat := 2 ^ 64 - 1

def UINT96_MAX : Nat := 2 ^ 96 - 1

def UINT192_MAX : Nat := 2 ^ 192 - 1

def UINT256_MAX : Nat := 2 ^ 256 - 1

def INT256_MAX : Nat := 2 ^ 255 - 1

/-- OpenZeppelin `Math.mulDiv(..., Floor)`. Denominator-zero is totalized here;
    successful specs exclude every source path on which Solidity would divide
    by zero. -/
def mulDivFloor (x y denominator : Nat) : Nat :=
  if denominator = 0 then 0 else x * y / denominator

/-- OpenZeppelin `Math.mulDiv(..., Ceil)`. -/
def mulDivCeil (x y denominator : Nat) : Nat :=
  if denominator = 0 then 0
  else
    let numerator := x * y
    if numerator = 0 then 0 else (numerator + denominator - 1) / denominator

/-- Solidity's explicit `uint32(x)` cast keeps the low 32 bits. -/
def uint32Cast (x : Nat) : Nat := x % (2 ^ 32)

/-- `Math.saturatingSub`. -/
def saturatingSub (a b : Nat) : Nat := a - b

/-- `UnitsMathLib.computeNAVDelta`. -/
def computeNAVDelta (current previous : Nat) : Int :=
  Int.ofNat current - Int.ofNat previous

/-- Source enum `MarketState`. -/
inductive MarketState where
  | perpetual
  | fixedTerm
  deriving Repr, DecidableEq

/-- Storage fields read by `_previewSyncTrancheAccounting`.

Names mirror `RoycoAccountantState` without the Solidity `last` prefix only
where the source consumes a configuration rather than a checkpoint. -/
structure AccountantState where
  lastMarketState : MarketState
  lastSTRawNAV : Nat
  lastJTRawNAV : Nat
  lastSTEffectiveNAV : Nat
  lastJTEffectiveNAV : Nat
  lastSTImpermanentLoss : Nat
  lastJTImpermanentLoss : Nat
  stNAVDustTolerance : Nat
  jtNAVDustTolerance : Nat
  stProtocolFeeWAD : Nat
  jtProtocolFeeWAD : Nat
  yieldShareProtocolFeeWAD : Nat
  lastDistributionTimestamp : Nat
  fixedTermEndTimestamp : Nat
  fixedTermDurationSeconds : Nat
  betaWAD : Nat
  coverageWAD : Nat
  liquidationUtilizationWAD : Nat
  deriving Repr, DecidableEq

/-- Call arguments plus the two environmental reads used by the view function. -/
structure SyncInput where
  stRawNAV : Nat
  jtRawNAV : Nat
  twJTYieldShareAccruedWAD : Nat
  timestamp : Nat
  instantaneousJTYieldShareWAD : Nat
  deriving Repr, DecidableEq

/-- Claim split and signed deltas computed in source lines 424-451. -/
structure EffectiveDeltas where
  stClaimOnJTRawNAV : Nat
  jtClaimOnSTRawNAV : Nat
  stClaimOnSTRawNAV : Nat
  deltaSTRawNAV : Int
  deltaJTRawNAV : Int
  deltaSTClaimOnSTRawNAV : Int
  deltaSTClaimOnJTRawNAV : Int
  deltaSTEffectiveNAV : Int
  deltaJTEffectiveNAV : Int
  deriving Repr, DecidableEq

/--
`_attributeDeltaToClaimOnRawNAV`: floor the unsigned magnitude and reapply the
sign. The complementary tranche therefore receives all signed rounding residual.
-/
def attributeDeltaToClaimOnRawNAV
    (delta : Int) (claimOnTrancheRawNAV lastTrancheRawNAV : Nat) : Int :=
  if delta = 0 ∨ claimOnTrancheRawNAV = 0 ∨ lastTrancheRawNAV = 0 then
    0
  else
    let attributedMagnitude := delta.natAbs * claimOnTrancheRawNAV / lastTrancheRawNAV
    if delta < 0 then -Int.ofNat attributedMagnitude else Int.ofNat attributedMagnitude

/-- Source lines 424-451, including the zero-last-ST-raw special case and JT
    residual attribution. -/
def computeEffectiveDeltas (s : AccountantState) (input : SyncInput) : EffectiveDeltas :=
  let stClaimOnJTRawNAV := saturatingSub s.lastSTEffectiveNAV s.lastSTRawNAV
  let jtClaimOnSTRawNAV := saturatingSub s.lastJTEffectiveNAV s.lastJTRawNAV
  let stClaimOnSTRawNAV := s.lastSTRawNAV - jtClaimOnSTRawNAV
  let deltaSTRawNAV := computeNAVDelta input.stRawNAV s.lastSTRawNAV
  let deltaJTRawNAV := computeNAVDelta input.jtRawNAV s.lastJTRawNAV
  let deltaSTClaimOnSTRawNAV :=
    if s.lastSTRawNAV = 0 then
      if s.lastSTEffectiveNAV > 0 then deltaSTRawNAV else 0
    else
      attributeDeltaToClaimOnRawNAV deltaSTRawNAV stClaimOnSTRawNAV s.lastSTRawNAV
  let deltaSTClaimOnJTRawNAV :=
    attributeDeltaToClaimOnRawNAV deltaJTRawNAV stClaimOnJTRawNAV s.lastJTRawNAV
  let deltaSTEffectiveNAV := deltaSTClaimOnSTRawNAV + deltaSTClaimOnJTRawNAV
  let deltaJTEffectiveNAV := deltaSTRawNAV + deltaJTRawNAV - deltaSTEffectiveNAV
  {
    stClaimOnJTRawNAV := stClaimOnJTRawNAV
    jtClaimOnSTRawNAV := jtClaimOnSTRawNAV
    stClaimOnSTRawNAV := stClaimOnSTRawNAV
    deltaSTRawNAV := deltaSTRawNAV
    deltaJTRawNAV := deltaJTRawNAV
    deltaSTClaimOnSTRawNAV := deltaSTClaimOnSTRawNAV
    deltaSTClaimOnJTRawNAV := deltaSTClaimOnJTRawNAV
    deltaSTEffectiveNAV := deltaSTEffectiveNAV
    deltaJTEffectiveNAV := deltaJTEffectiveNAV
  }

/-- Mutable memory locals between source lines 454 and 583. -/
structure AllocationState where
  stEffectiveNAV : Nat
  jtEffectiveNAV : Nat
  stImpermanentLoss : Nat
  jtImpermanentLoss : Nat
  stProtocolFeeAccrued : Nat
  jtProtocolFeeAccrued : Nat
  jtNetGain : Nat
  yieldDistributed : Bool
  deriving Repr, DecidableEq

def initialAllocationState (s : AccountantState) : AllocationState where
  stEffectiveNAV := s.lastSTEffectiveNAV
  jtEffectiveNAV := s.lastJTEffectiveNAV
  stImpermanentLoss := s.lastSTImpermanentLoss
  jtImpermanentLoss := s.lastJTImpermanentLoss
  stProtocolFeeAccrued := 0
  jtProtocolFeeAccrued := 0
  jtNetGain := 0
  yieldDistributed := false

/-- Source lines 467-504: apply JT effective loss/gain before the ST leg. -/
def applyJTEffectiveDelta
    (s : AccountantState) (deltaJTEffectiveNAV : Int) : AllocationState :=
  let state := initialAllocationState s
  let dust := s.stNAVDustTolerance + s.jtNAVDustTolerance
  if deltaJTEffectiveNAV < 0 then
    let jtLoss := deltaJTEffectiveNAV.natAbs
    let jtAbsorbableLoss := min jtLoss state.jtEffectiveNAV
    let residualLoss := jtLoss - jtAbsorbableLoss
    {
      state with
      jtEffectiveNAV := state.jtEffectiveNAV - jtAbsorbableLoss
      stEffectiveNAV := state.stEffectiveNAV - residualLoss
      stImpermanentLoss := state.stImpermanentLoss + residualLoss
    }
  else if deltaJTEffectiveNAV > 0 then
    let jtGain := deltaJTEffectiveNAV.natAbs
    let stImpermanentLossRecovery := min jtGain state.stImpermanentLoss
    let jtNetGain := jtGain - stImpermanentLossRecovery
    let jtProtocolFeeAccrued :=
      if jtNetGain > dust then mulDivFloor jtNetGain s.jtProtocolFeeWAD WAD else 0
    {
      state with
      stImpermanentLoss := state.stImpermanentLoss - stImpermanentLossRecovery
      stEffectiveNAV := state.stEffectiveNAV + stImpermanentLossRecovery
      jtEffectiveNAV := state.jtEffectiveNAV + jtNetGain
      jtProtocolFeeAccrued := jtProtocolFeeAccrued
      jtNetGain := jtNetGain
    }
  else
    state

/-- Source lines 556-568. The external instantaneous YDM result is supplied in
    `input` and capped at WAD exactly as in Solidity. -/
def computeYieldShare (s : AccountantState) (input : SyncInput) (stGain : Nat) : Nat :=
  let elapsed := input.timestamp - s.lastDistributionTimestamp
  if elapsed = 0 then
    let instantaneousJTYieldShareWAD := min input.instantaneousJTYieldShareWAD WAD
    mulDivFloor stGain instantaneousJTYieldShareWAD WAD
  else
    mulDivFloor stGain input.twJTYieldShareAccruedWAD (elapsed * WAD)

/-- Source lines 506-583: apply ST effective loss/gain after the JT leg. -/
def applySTEffectiveDelta
    (s : AccountantState)
    (input : SyncInput)
    (afterJT : AllocationState)
    (deltaSTEffectiveNAV : Int) : AllocationState :=
  let dust := s.stNAVDustTolerance + s.jtNAVDustTolerance
  if deltaSTEffectiveNAV < 0 then
    let stLoss := deltaSTEffectiveNAV.natAbs
    let coverageApplied := min stLoss afterJT.jtEffectiveNAV
    let jtNetGain :=
      if afterJT.jtProtocolFeeAccrued ≠ 0 then
        saturatingSub afterJT.jtNetGain coverageApplied
      else
        afterJT.jtNetGain
    let jtProtocolFeeAccrued :=
      if afterJT.jtProtocolFeeAccrued ≠ 0 then
        if jtNetGain > dust then mulDivFloor jtNetGain s.jtProtocolFeeWAD WAD else 0
      else
        afterJT.jtProtocolFeeAccrued
    let residualSTLoss := stLoss - coverageApplied
    {
      afterJT with
      jtEffectiveNAV := afterJT.jtEffectiveNAV - coverageApplied
      jtImpermanentLoss := afterJT.jtImpermanentLoss + coverageApplied
      stEffectiveNAV := afterJT.stEffectiveNAV - residualSTLoss
      stImpermanentLoss := afterJT.stImpermanentLoss + residualSTLoss
      jtProtocolFeeAccrued := jtProtocolFeeAccrued
      jtNetGain := jtNetGain
    }
  else if deltaSTEffectiveNAV > 0 then
    let stGain := deltaSTEffectiveNAV.natAbs
    let stImpermanentLossRecovery := min stGain afterJT.stImpermanentLoss
    let afterSTILRecovery := stGain - stImpermanentLossRecovery
    let jtImpermanentLossRecovery := min afterSTILRecovery afterJT.jtImpermanentLoss
    let residualSTGain := afterSTILRecovery - jtImpermanentLossRecovery
    let yieldDistributed := residualSTGain > dust
    let yieldShare :=
      if residualSTGain = 0 then 0 else computeYieldShare s input residualSTGain
    let stResidualAfterYieldShare := residualSTGain - yieldShare
    let jtProtocolFeeAccrued :=
      if yieldDistributed then
        afterJT.jtProtocolFeeAccrued +
          mulDivFloor yieldShare s.yieldShareProtocolFeeWAD WAD
      else
        afterJT.jtProtocolFeeAccrued
    let stProtocolFeeAccrued :=
      if yieldDistributed then
        mulDivFloor stResidualAfterYieldShare s.stProtocolFeeWAD WAD
      else
        0
    {
      afterJT with
      stEffectiveNAV :=
        afterJT.stEffectiveNAV + stImpermanentLossRecovery + stResidualAfterYieldShare
      jtEffectiveNAV :=
        afterJT.jtEffectiveNAV + jtImpermanentLossRecovery + yieldShare
      stImpermanentLoss := afterJT.stImpermanentLoss - stImpermanentLossRecovery
      jtImpermanentLoss := afterJT.jtImpermanentLoss - jtImpermanentLossRecovery
      stProtocolFeeAccrued := stProtocolFeeAccrued
      jtProtocolFeeAccrued := jtProtocolFeeAccrued
      yieldDistributed := yieldDistributed
    }
  else
    afterJT

/-- `UtilsLib.computeUtilization`, including ceil rounding and the nonzero
    exposure / zero JT-buffer `uint256.max` sentinel. -/
def computeUtilization
    (stRawNAV jtRawNAV betaWAD coverageWAD jtEffectiveNAV : Nat) : Nat :=
  let totalCoveredExposure := stRawNAV + mulDivCeil jtRawNAV betaWAD WAD
  if totalCoveredExposure = 0 then 0
  else if jtEffectiveNAV = 0 then UINT256_MAX
  else mulDivCeil coverageWAD totalCoveredExposure jtEffectiveNAV

/-- Final memory return fields from `SyncedAccountingState`. -/
structure SyncedAccountingState where
  marketState : MarketState
  stRawNAV : Nat
  jtRawNAV : Nat
  stEffectiveNAV : Nat
  jtEffectiveNAV : Nat
  stImpermanentLoss : Nat
  jtImpermanentLoss : Nat
  stProtocolFeeAccrued : Nat
  jtProtocolFeeAccrued : Nat
  utilizationWAD : Nat
  fixedTermEndTimestamp : Nat
  coverageWAD : Nat
  betaWAD : Nat
  liquidationUtilizationWAD : Nat
  deriving Repr, DecidableEq

/-- Source lines 588-637, kept separate so the NAV-conservation checkpoint is
    observable before forced-perpetual JT-liability erasure. -/
structure MarketResolution where
  marketState : MarketState
  jtImpermanentLoss : Nat
  stProtocolFeeAccrued : Nat
  jtProtocolFeeAccrued : Nat
  fixedTermEndTimestamp : Nat
  jtImpermanentLossErased : Nat
  deriving Repr, DecidableEq

/-- The exact disjunction at source lines 600-603. -/
def forcedPerpetual
    (s : AccountantState)
    (input : SyncInput)
    (allocated : AllocationState)
    (utilizationWAD : Nat) : Bool :=
  s.fixedTermDurationSeconds == 0 ||
  (s.lastMarketState == MarketState.fixedTerm && s.fixedTermEndTimestamp <= input.timestamp) ||
  utilizationWAD >= s.liquidationUtilizationWAD ||
  allocated.stImpermanentLoss != 0

/-- Source market-state transition, including fixed-term fee zeroing and the
    explicit forced-perpetual `jtImpermanentLoss` erasure. -/
def resolveMarketState
    (s : AccountantState)
    (input : SyncInput)
    (allocated : AllocationState)
    (utilizationWAD : Nat) : MarketResolution :=
  let dust := s.stNAVDustTolerance + s.jtNAVDustTolerance
  if forcedPerpetual s input allocated utilizationWAD then
    {
      marketState := MarketState.perpetual
      jtImpermanentLoss := 0
      stProtocolFeeAccrued := allocated.stProtocolFeeAccrued
      jtProtocolFeeAccrued := allocated.jtProtocolFeeAccrued
      fixedTermEndTimestamp := 0
      jtImpermanentLossErased := allocated.jtImpermanentLoss
    }
  else if allocated.jtImpermanentLoss <= dust then
    if s.lastMarketState = MarketState.perpetual ∨ allocated.jtImpermanentLoss = 0 then
      {
        marketState := MarketState.perpetual
        jtImpermanentLoss := allocated.jtImpermanentLoss
        stProtocolFeeAccrued := allocated.stProtocolFeeAccrued
        jtProtocolFeeAccrued := allocated.jtProtocolFeeAccrued
        fixedTermEndTimestamp := 0
        jtImpermanentLossErased := 0
      }
    else
      {
        marketState := MarketState.fixedTerm
        jtImpermanentLoss := allocated.jtImpermanentLoss
        stProtocolFeeAccrued := 0
        jtProtocolFeeAccrued := 0
        fixedTermEndTimestamp := s.fixedTermEndTimestamp
        jtImpermanentLossErased := 0
      }
  else
    {
      marketState := MarketState.fixedTerm
      jtImpermanentLoss := allocated.jtImpermanentLoss
      stProtocolFeeAccrued := 0
      jtProtocolFeeAccrued := 0
      fixedTermEndTimestamp :=
        if s.lastMarketState = MarketState.perpetual then
          uint32Cast (input.timestamp + s.fixedTermDurationSeconds)
        else
          s.fixedTermEndTimestamp
      jtImpermanentLossErased := 0
    }

/-- Ghost trace for the exact recovery identities selected in Phase 1.

These values are not extra contract state. They name source intermediates before the
residual ST gain is split between tranches. -/
structure RecoveryTrace where
  stRecoveryFromJT : Nat
  residualJTGain : Nat
  stRecoveryFromST : Nat
  jtRecoveryFromST : Nat
  residualSTYield : Nat
  deriving Repr, DecidableEq

def computeRecoveryTrace
    (s : AccountantState)
    (deltas : EffectiveDeltas)
    (afterJT : AllocationState) : RecoveryTrace :=
  let jtGain :=
    if deltas.deltaJTEffectiveNAV > 0 then deltas.deltaJTEffectiveNAV.natAbs else 0
  let stRecoveryFromJT := min jtGain s.lastSTImpermanentLoss
  let residualJTGain := jtGain - stRecoveryFromJT
  let stGain :=
    if deltas.deltaSTEffectiveNAV > 0 then deltas.deltaSTEffectiveNAV.natAbs else 0
  let stRecoveryFromST := min stGain afterJT.stImpermanentLoss
  let afterSTRecovery := stGain - stRecoveryFromST
  let jtRecoveryFromST := min afterSTRecovery afterJT.jtImpermanentLoss
  {
    stRecoveryFromJT := stRecoveryFromJT
    residualJTGain := residualJTGain
    stRecoveryFromST := stRecoveryFromST
    jtRecoveryFromST := jtRecoveryFromST
    residualSTYield := afterSTRecovery - jtRecoveryFromST
  }

/-- Full return value with ghost observables for proof and translation audit. -/
structure PreviewSyncResult where
  state : SyncedAccountingState
  initialMarketState : MarketState
  yieldDistributed : Bool
  jtImpermanentLossErased : Nat
  effectiveDeltas : EffectiveDeltas
  recoveryTrace : RecoveryTrace
  afterJT : AllocationState
  allocationState : AllocationState
  deriving Repr, DecidableEq

/-- Source-close model of `_previewSyncTrancheAccounting` in execution order. -/
def previewSyncTrancheAccounting
    (s : AccountantState) (input : SyncInput) : PreviewSyncResult :=
  let effectiveDeltas := computeEffectiveDeltas s input
  let afterJT := applyJTEffectiveDelta s effectiveDeltas.deltaJTEffectiveNAV
  let recoveryTrace := computeRecoveryTrace s effectiveDeltas afterJT
  let allocated :=
    applySTEffectiveDelta s input afterJT effectiveDeltas.deltaSTEffectiveNAV
  -- Solidity checks NAV conservation at this exact boundary (line 585), before
  -- market-state resolution can explicitly erase JT impermanent loss.
  let utilizationWAD :=
    computeUtilization input.stRawNAV input.jtRawNAV s.betaWAD s.coverageWAD
      allocated.jtEffectiveNAV
  let market := resolveMarketState s input allocated utilizationWAD
  {
    state := {
      marketState := market.marketState
      stRawNAV := input.stRawNAV
      jtRawNAV := input.jtRawNAV
      stEffectiveNAV := allocated.stEffectiveNAV
      jtEffectiveNAV := allocated.jtEffectiveNAV
      stImpermanentLoss := allocated.stImpermanentLoss
      jtImpermanentLoss := market.jtImpermanentLoss
      stProtocolFeeAccrued := market.stProtocolFeeAccrued
      jtProtocolFeeAccrued := market.jtProtocolFeeAccrued
      utilizationWAD := utilizationWAD
      fixedTermEndTimestamp := market.fixedTermEndTimestamp
      coverageWAD := s.coverageWAD
      betaWAD := s.betaWAD
      liquidationUtilizationWAD := s.liquidationUtilizationWAD
    }
    initialMarketState := s.lastMarketState
    yieldDistributed := allocated.yieldDistributed
    jtImpermanentLossErased := market.jtImpermanentLossErased
    effectiveDeltas := effectiveDeltas
    recoveryTrace := recoveryTrace
    afterJT := afterJT
    allocationState := allocated
  }

end Benchmark.Cases.Royco.DawnValuationRecovery
