import Mathlib.Data.Nat.Basic

/-!
Arithmetic model of the T3tris high-water-mark performance-fee computation.

Upstream: t3tris-finance/T3tris-Vault
Commit:   89ad64a8e945214cd40a18db146e1feed83e417f
Files:    src/libraries/feature/FeatureFeesLib.sol
          src/libraries/feature/FeatureSettlementLib.sol
          src/libraries/release/ReleaseFeesLib.sol

In scope:
- `FeatureFeesLib._computeLastPeriodFeesAndUpdateResult`
- the HWM ratchet used by `ReleaseFeesLib.computeAndRecordAccruedFees`
  and `FeatureSettlementLib._updateSettlementValues`

Simplifications:
- Arithmetic is modeled over `Nat`, not `Uint256`. Solidity 0.8 overflow and
  raw-sub underflow are therefore successful-path preconditions in `Specs.lean`.
- `_computeManagementFee` is abstracted into explicit management-fee assets and
  shares. This keeps the target theorem on the performance-fee/HWM surface while
  preserving the Solidity ordering: management fee shares are added before the
  performance PPS trigger is evaluated.
- External valuation, oracle, silo, transfer, async-flow, and ERC20 mint/burn
  mechanics are not modeled. Each settlement step receives the observed gross
  assets as an input and carries forward the fee-accounted gross supply and HWM.
- The Solidity `LastPeriodData.updatedPps` field is overwritten after
  performance fee shares are added. The model keeps an extra ghost observable
  `prePerformancePps` so specs can state the trigger/base condition directly.
- The zero-supply lifecycle HWM reanchor is factored into `persistHighWaterMark`.
  The main no-double-charge trajectory uses the non-reanchor branch.
- Division by zero is totalized to zero in helper functions. Specs include
  nonzero-denominator/successful-path assumptions where they matter.
- `uint128` and `uint64` bounds are not encoded in the structures. They are
  proof preconditions for any later Uint256/ABI fidelity pass.
-/

namespace Benchmark.Cases.T3tris.HwmPerformanceFee

def WAD : Nat := 10 ^ 18

def absDist (a b : Nat) : Nat :=
  if a < b then b - a else a - b

def fullMulDiv (x y denominator : Nat) : Nat :=
  if denominator = 0 then 0 else x * y / denominator

def fullMulDivUp (x y denominator : Nat) : Nat :=
  if denominator = 0 then 0
  else
    let numerator := x * y
    if numerator = 0 then 0 else (numerator + denominator - 1) / denominator

def computeFee (value feeWad : Nat) : Nat :=
  if feeWad = 0 then 0 else fullMulDivUp value feeWad WAD

structure GrossTvlData where
  totalAssets : Nat
  totalSupply : Nat
  deriving Repr, DecidableEq

structure NetTvlData where
  totalNetAssets : Nat
  totalNetSupply : Nat
  deriving Repr, DecidableEq

structure PeriodFeesParams where
  unclaimedSharesFee : Nat
  ppsHighWaterMark : Nat
  performanceFeeWad : Nat
  deriving Repr, DecidableEq

structure ManagementFeeModel where
  managementFeeAssets : Nat
  managementFeeShares : Nat
  deriving Repr, DecidableEq

def noManagementFee : ManagementFeeModel where
  managementFeeAssets := 0
  managementFeeShares := 0

structure LastPeriodData where
  oldTotalNetAssets : Nat
  oldTotalNetSupply : Nat
  managementFeeAssets : Nat
  managementFeeShares : Nat
  performanceFeeAssets : Nat
  performanceFeeShares : Nat
  periodFeeShares : Nat
  pnl : Nat
  prePerformancePps : Nat
  updatedPps : Nat
  isProfit : Bool
  deriving Repr, DecidableEq

structure PeriodFeesResult where
  grossTvlData : GrossTvlData
  lastPeriodData : LastPeriodData
  netTvlData : NetTvlData
  deriving Repr, DecidableEq

def oldTotalNetSupply (gross : GrossTvlData) (params : PeriodFeesParams) : Nat :=
  gross.totalSupply - params.unclaimedSharesFee

def oldTotalNetAssets (gross : GrossTvlData) (params : PeriodFeesParams) : Nat :=
  if oldTotalNetSupply gross params = 0 then
    gross.totalAssets
  else
    fullMulDiv gross.totalAssets (oldTotalNetSupply gross params) gross.totalSupply

def supplyAfterManagement (gross : GrossTvlData) (managementFee : ManagementFeeModel) : Nat :=
  gross.totalSupply + managementFee.managementFeeShares

def prePerformancePps (gross : GrossTvlData) (managementFee : ManagementFeeModel) : Nat :=
  if supplyAfterManagement gross managementFee = 0 then
    WAD
  else
    fullMulDiv gross.totalAssets WAD (supplyAfterManagement gross managementFee)

def isPerformanceProfit
    (gross : GrossTvlData)
    (params : PeriodFeesParams)
    (managementFee : ManagementFeeModel) : Bool :=
  decide (prePerformancePps gross managementFee > params.ppsHighWaterMark)

def performancePnl
    (gross : GrossTvlData)
    (params : PeriodFeesParams)
    (managementFee : ManagementFeeModel) : Nat :=
  fullMulDiv
    (absDist (prePerformancePps gross managementFee) params.ppsHighWaterMark)
    (oldTotalNetSupply gross params)
    WAD

def currentNetAssets
    (gross : GrossTvlData)
    (params : PeriodFeesParams)
    (managementFee : ManagementFeeModel) : Nat :=
  if supplyAfterManagement gross managementFee = 0 then
    0
  else
    fullMulDiv gross.totalAssets (oldTotalNetSupply gross params)
      (supplyAfterManagement gross managementFee)

def performanceFeeAssetsCandidate
    (gross : GrossTvlData)
    (params : PeriodFeesParams)
    (managementFee : ManagementFeeModel) : Nat :=
  if isPerformanceProfit gross params managementFee then
    computeFee (performancePnl gross params managementFee) params.performanceFeeWad
  else
    0

def performanceFeeSharesCandidate
    (gross : GrossTvlData)
    (params : PeriodFeesParams)
    (managementFee : ManagementFeeModel) : Nat :=
  if isPerformanceProfit gross params managementFee then
    if supplyAfterManagement gross managementFee = 0 then
      0
    else if performanceFeeAssetsCandidate gross params managementFee <
        currentNetAssets gross params managementFee then
      fullMulDivUp
        (performanceFeeAssetsCandidate gross params managementFee)
        (supplyAfterManagement gross managementFee)
        (currentNetAssets gross params managementFee -
          performanceFeeAssetsCandidate gross params managementFee)
    else
      0
  else
    0

def performanceFeeAssets
    (gross : GrossTvlData)
    (params : PeriodFeesParams)
    (managementFee : ManagementFeeModel) : Nat :=
  if performanceFeeSharesCandidate gross params managementFee = 0 then
    0
  else
    performanceFeeAssetsCandidate gross params managementFee

def periodFeeShares
    (gross : GrossTvlData)
    (params : PeriodFeesParams)
    (managementFee : ManagementFeeModel) : Nat :=
  managementFee.managementFeeShares + performanceFeeSharesCandidate gross params managementFee

def finalSupply
    (gross : GrossTvlData)
    (params : PeriodFeesParams)
    (managementFee : ManagementFeeModel) : Nat :=
  supplyAfterManagement gross managementFee +
    performanceFeeSharesCandidate gross params managementFee

def finalUpdatedPps
    (gross : GrossTvlData)
    (params : PeriodFeesParams)
    (managementFee : ManagementFeeModel) : Nat :=
  if finalSupply gross params managementFee = 0 then
    WAD
  else
    fullMulDiv gross.totalAssets WAD (finalSupply gross params managementFee)

def totalNetAssets
    (gross : GrossTvlData)
    (params : PeriodFeesParams)
    (managementFee : ManagementFeeModel) : Nat :=
  if finalSupply gross params managementFee = 0 then
    gross.totalAssets
  else
    fullMulDiv gross.totalAssets (oldTotalNetSupply gross params)
      (finalSupply gross params managementFee)

/--
Source-close arithmetic slice of
`FeatureFeesLib._computeLastPeriodFeesAndUpdateResult`.

The `managementFee` input represents the result of `_computeManagementFee`;
the body preserves the source ordering from that point onward.
-/
def computeLastPeriodFeesAndUpdateResult
    (gross : GrossTvlData)
    (params : PeriodFeesParams)
    (managementFee : ManagementFeeModel := noManagementFee) :
    PeriodFeesResult :=
  {
    grossTvlData := {
      totalAssets := gross.totalAssets
      totalSupply := finalSupply gross params managementFee
    }
    lastPeriodData := {
      oldTotalNetAssets := oldTotalNetAssets gross params
      oldTotalNetSupply := oldTotalNetSupply gross params
      managementFeeAssets := managementFee.managementFeeAssets
      managementFeeShares := managementFee.managementFeeShares
      performanceFeeAssets := performanceFeeAssets gross params managementFee
      performanceFeeShares := performanceFeeSharesCandidate gross params managementFee
      periodFeeShares := periodFeeShares gross params managementFee
      pnl := performancePnl gross params managementFee
      prePerformancePps := prePerformancePps gross managementFee
      updatedPps := finalUpdatedPps gross params managementFee
      isProfit := isPerformanceProfit gross params managementFee
    }
    netTvlData := {
      totalNetAssets := totalNetAssets gross params managementFee
      totalNetSupply := oldTotalNetSupply gross params
    }
  }

structure FeeState where
  grossSupply : Nat
  unclaimedSharesFee : Nat
  ppsHighWaterMark : Nat
  performanceFeeWad : Nat
  deriving Repr, DecidableEq

def persistHighWaterMark
    (oldHighWaterMark updatedPps preMintGrossSupply depositMintedVaultShares : Nat) : Nat :=
  if preMintGrossSupply = 0 /\ depositMintedVaultShares > 0 then
    WAD
  else
    max oldHighWaterMark updatedPps

def recordAccruedFeesNoReanchor (s : FeeState) (result : PeriodFeesResult) : FeeState :=
  {
    grossSupply := result.grossTvlData.totalSupply
    unclaimedSharesFee := s.unclaimedSharesFee + result.lastPeriodData.periodFeeShares
    ppsHighWaterMark := max s.ppsHighWaterMark result.lastPeriodData.updatedPps
    performanceFeeWad := s.performanceFeeWad
  }

def periodStepNoReanchor
    (s : FeeState)
    (totalAssets : Nat)
    (managementFee : ManagementFeeModel := noManagementFee) :
    Prod FeeState PeriodFeesResult :=
  let result := computeLastPeriodFeesAndUpdateResult
    {
      totalAssets := totalAssets
      totalSupply := s.grossSupply
    }
    {
      unclaimedSharesFee := s.unclaimedSharesFee
      ppsHighWaterMark := s.ppsHighWaterMark
      performanceFeeWad := s.performanceFeeWad
    }
    managementFee
  (recordAccruedFeesNoReanchor s result, result)

end Benchmark.Cases.T3tris.HwmPerformanceFee
