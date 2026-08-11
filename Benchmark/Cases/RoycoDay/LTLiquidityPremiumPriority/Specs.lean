import Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority.Contract

namespace Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority

/-- Successful pure-accountant path, including the source require boundaries. -/
def successfulSyncDomain
    (last : AccountingState)
    (currentCollateralNAV : Nat)
    (yieldCfg : YieldConfig) : Prop :=
  let gain := currentCollateralNAV - last.collateralNAV
  let repaid := min gain last.jtImpermanentLoss
  let residual := gain - repaid
  let stGain := residualSTGain last currentCollateralNAV
  let jtPremium := grossPremium stGain yieldCfg.twJTYieldShareAccruedWAD
    yieldCfg.elapsedSinceLastPremiumPayments
  let lptPremium := grossPremium stGain yieldCfg.twLPTYieldShareAccruedWAD
    yieldCfg.elapsedSinceLastPremiumPayments
  let jtGain := residual - stGain
  last.conserves ∧
    yieldCfg.valid ∧
    (currentCollateralNAV < last.collateralNAV →
      last.collateralNAV - currentCollateralNAV -
        min (last.collateralNAV - currentCollateralNAV)
          last.jtEffectiveNAV ≤ last.stEffectiveNAV ∧
      last.jtImpermanentLoss +
        min (last.collateralNAV - currentCollateralNAV)
          last.jtEffectiveNAV ≤ UINT256_MAX) ∧
    (last.collateralNAV < currentCollateralNAV →
      stGain ≤ residual ∧
      jtPremium + lptPremium ≤ stGain ∧
      last.collateralNAV + repaid ≤ UINT256_MAX ∧
      last.stEffectiveNAV + stGain ≤ UINT256_MAX ∧
      last.jtEffectiveNAV + repaid ≤ UINT256_MAX ∧
      last.jtEffectiveNAV + repaid + jtGain ≤ UINT256_MAX ∧
      last.jtEffectiveNAV + repaid + jtGain + jtPremium ≤ UINT256_MAX)

/-!
## Solidity refinement boundary

The executable model uses unbounded naturals. Source-facing theorems require exact
`uint256`/`int256` encodings, `uint128` accumulator bounds, successful checked
add/sub results, and bounded full-precision `mulDiv` quotients.
-/

def AccountingState.uint256Bounded (s : AccountingState) : Prop :=
  s.collateralNAV ≤ UINT256_MAX ∧
    s.lptRawNAV ≤ UINT256_MAX ∧
    s.stEffectiveNAV ≤ UINT256_MAX ∧
    s.jtEffectiveNAV ≤ UINT256_MAX ∧
    s.jtImpermanentLoss ≤ UINT256_MAX ∧
    s.stEffectiveNAV + s.jtEffectiveNAV ≤ UINT256_MAX

def YieldConfig.uintBounded (cfg : YieldConfig) : Prop :=
  cfg.elapsedSinceLastPremiumPayments ≤ UINT256_MAX ∧
    cfg.twJTYieldShareAccruedWAD ≤ UINT128_MAX ∧
    cfg.twLPTYieldShareAccruedWAD ≤ UINT128_MAX ∧
    cfg.elapsedSinceLastPremiumPayments * WAD ≤ UINT256_MAX ∧
    cfg.stProtocolFeeWAD ≤ UINT64_MAX ∧
    cfg.jtProtocolFeeWAD ≤ UINT64_MAX ∧
    cfg.jtYieldShareProtocolFeeWAD ≤ UINT64_MAX ∧
    cfg.lptYieldShareProtocolFeeWAD ≤ UINT64_MAX

def SyncConfig.uint256Bounded (cfg : SyncConfig) : Prop :=
  cfg.dustTolerance ≤ UINT256_MAX ∧
    cfg.minCoverageWAD ≤ UINT64_MAX ∧
    cfg.minLiquidityWAD ≤ UINT64_MAX ∧
    cfg.coverageLiquidationUtilizationWAD ≤ UINT256_MAX

def YieldOutputs.uint256Bounded (outputs : YieldOutputs) : Prop :=
  outputs.lptLiquidityPremium ≤ UINT256_MAX ∧
    outputs.stProtocolFee ≤ UINT256_MAX ∧
    outputs.jtProtocolFee ≤ UINT256_MAX ∧
    outputs.lptProtocolFee ≤ UINT256_MAX

def SyncResult.uint256Bounded (result : SyncResult) : Prop :=
  result.accounting.uint256Bounded ∧
    result.outputs.uint256Bounded ∧
    result.jtImpermanentLossRepaid ≤ UINT256_MAX ∧
    result.remainingImpermanentLossBeforeTransition ≤ UINT256_MAX ∧
    result.residualGainAfterRepayment ≤ UINT256_MAX ∧
    result.stGain ≤ UINT256_MAX ∧
    result.jtGain ≤ UINT256_MAX ∧
    result.jtRiskPremiumGross ≤ UINT256_MAX ∧
    result.jtYieldShareProtocolFee ≤ UINT256_MAX ∧
    result.jtLossAbsorbed ≤ UINT256_MAX ∧
    result.residualSTLoss ≤ UINT256_MAX ∧
    result.coverageUtilization ≤ UINT256_MAX ∧
    result.liquidityUtilization ≤ UINT256_MAX

def sourceSyncDomain
    (last : AccountingState)
    (currentCollateralNAV : Nat)
    (syncCfg : SyncConfig)
    (yieldCfg : YieldConfig) : Prop :=
  successfulSyncDomain last currentCollateralNAV yieldCfg ∧
    last.uint256Bounded ∧
    currentCollateralNAV ≤ UINT256_MAX ∧
    syncCfg.uint256Bounded ∧
    yieldCfg.uintBounded ∧
    (previewSyncTrancheAccounting
      last currentCollateralNAV syncCfg yieldCfg).uint256Bounded

def natUint256EncodingExact (n : Nat) : Prop :=
  (Verity.Core.Uint256.ofNat n).val = n

def int256EncodingExact (value : Int) : Prop :=
  ((Verity.Core.Int256.ofInt value : Verity.Core.Int256) : Int) = value

def natInt256EncodingExact (n : Nat) : Prop :=
  int256EncodingExact (Int.ofNat n)

def AccountingState.uint256EncodingExact (s : AccountingState) : Prop :=
  natUint256EncodingExact s.collateralNAV ∧
    natUint256EncodingExact s.lptRawNAV ∧
    natUint256EncodingExact s.stEffectiveNAV ∧
    natUint256EncodingExact s.jtEffectiveNAV ∧
    natUint256EncodingExact s.jtImpermanentLoss

def YieldConfig.uintEncodingExact (cfg : YieldConfig) : Prop :=
  natUint256EncodingExact cfg.elapsedSinceLastPremiumPayments ∧
    natUint256EncodingExact cfg.twJTYieldShareAccruedWAD ∧
    natUint256EncodingExact cfg.twLPTYieldShareAccruedWAD ∧
    natUint256EncodingExact cfg.stProtocolFeeWAD ∧
    natUint256EncodingExact cfg.jtProtocolFeeWAD ∧
    natUint256EncodingExact cfg.jtYieldShareProtocolFeeWAD ∧
    natUint256EncodingExact cfg.lptYieldShareProtocolFeeWAD

def SyncConfig.uint256EncodingExact (cfg : SyncConfig) : Prop :=
  natUint256EncodingExact cfg.dustTolerance ∧
    natUint256EncodingExact cfg.minCoverageWAD ∧
    natUint256EncodingExact cfg.minLiquidityWAD ∧
    natUint256EncodingExact cfg.coverageLiquidationUtilizationWAD

def YieldOutputs.uint256EncodingExact (outputs : YieldOutputs) : Prop :=
  natUint256EncodingExact outputs.lptLiquidityPremium ∧
    natUint256EncodingExact outputs.stProtocolFee ∧
    natUint256EncodingExact outputs.jtProtocolFee ∧
    natUint256EncodingExact outputs.lptProtocolFee

def SyncResult.uint256EncodingExact (result : SyncResult) : Prop :=
  result.accounting.uint256EncodingExact ∧
    result.outputs.uint256EncodingExact ∧
    natUint256EncodingExact result.jtImpermanentLossRepaid ∧
    natUint256EncodingExact result.remainingImpermanentLossBeforeTransition ∧
    natUint256EncodingExact result.residualGainAfterRepayment ∧
    natUint256EncodingExact result.stGain ∧
    natUint256EncodingExact result.jtGain ∧
    natUint256EncodingExact result.jtRiskPremiumGross ∧
    natUint256EncodingExact result.jtYieldShareProtocolFee ∧
    natUint256EncodingExact result.jtLossAbsorbed ∧
    natUint256EncodingExact result.residualSTLoss ∧
    natUint256EncodingExact result.coverageUtilization ∧
    natUint256EncodingExact result.liquidityUtilization

def checkedArithmeticRefinesNat : Prop :=
  ∀ a b : Nat,
    a ≤ UINT256_MAX → b ≤ UINT256_MAX →
    (a + b ≤ UINT256_MAX →
      Verity.Stdlib.Math.safeAdd
        (Verity.Core.Uint256.ofNat a) (Verity.Core.Uint256.ofNat b) =
          some (Verity.Core.Uint256.ofNat (a + b))) ∧
    (b ≤ a →
      Verity.Stdlib.Math.safeSub
        (Verity.Core.Uint256.ofNat a) (Verity.Core.Uint256.ofNat b) =
          some (Verity.Core.Uint256.ofNat (a - b)))

def fullPrecisionMulDivRefinesNat : Prop :=
  ∀ a b denominator : Nat,
    a ≤ UINT256_MAX → b ≤ UINT256_MAX → denominator ≤ UINT256_MAX →
    denominator ≠ 0 →
    (mulDivDown a b denominator ≤ UINT256_MAX →
      Verity.Stdlib.Math.mulDiv512Down?
        (Verity.Core.Uint256.ofNat a)
        (Verity.Core.Uint256.ofNat b)
        (Verity.Core.Uint256.ofNat denominator) =
          some (Verity.Core.Uint256.ofNat (mulDivDown a b denominator))) ∧
    (mulDivUp a b denominator ≤ UINT256_MAX →
      Verity.Stdlib.Math.mulDiv512Up?
        (Verity.Core.Uint256.ofNat a)
        (Verity.Core.Uint256.ofNat b)
        (Verity.Core.Uint256.ofNat denominator) =
          some (Verity.Core.Uint256.ofNat (mulDivUp a b denominator)))

def NatUint256RefinementSpec
    (last : AccountingState)
    (currentCollateralNAV : Nat)
    (syncCfg : SyncConfig)
    (yieldCfg : YieldConfig) : Prop :=
  let result := previewSyncTrancheAccounting
    last currentCollateralNAV syncCfg yieldCfg
  successfulSyncDomain last currentCollateralNAV yieldCfg ∧
    result.uint256Bounded ∧
    last.uint256EncodingExact ∧
    natUint256EncodingExact currentCollateralNAV ∧
    syncCfg.uint256EncodingExact ∧
    yieldCfg.uintEncodingExact ∧
    result.uint256EncodingExact ∧
    checkedArithmeticRefinesNat ∧
    fullPrecisionMulDivRefinesNat

/-- Collateral recovery repays `min(gain, IL)` before any residual yield. -/
def RecoveryBeforeYieldSpec
    (last : AccountingState)
    (gain : Nat)
    (syncCfg : SyncConfig)
    (yieldCfg : YieldConfig) : Prop :=
  let result := previewSyncTrancheAccounting
    last (last.collateralNAV + gain) syncCfg yieldCfg
  result.jtImpermanentLossRepaid = min gain last.jtImpermanentLoss ∧
    result.remainingImpermanentLossBeforeTransition =
      last.jtImpermanentLoss - result.jtImpermanentLossRepaid ∧
    result.residualGainAfterRepayment =
      gain - result.jtImpermanentLossRepaid ∧
    (gain ≤ last.jtImpermanentLoss →
      result.residualGainAfterRepayment = 0 ∧
      result.stGain = 0 ∧ result.jtGain = 0 ∧
      result.jtRiskPremiumGross = 0 ∧
      result.outputs = YieldOutputs.zero)

/-- The two gross yield shares cannot exceed the senior gain. -/
def CombinedPremiumBoundSpec (stGain : Nat) (cfg : YieldConfig) : Prop :=
  grossPremium stGain cfg.twJTYieldShareAccruedWAD
      cfg.elapsedSinceLastPremiumPayments +
    grossPremium stGain cfg.twLPTYieldShareAccruedWAD
      cfg.elapsedSinceLastPremiumPayments ≤ stGain

/-- Changing only LPT's premium numerator cannot change ST/JT accounting. -/
def LPTPremiumCoverageNeutralSpec
    (last : AccountingState)
    (currentCollateralNAV : Nat)
    (syncCfg : SyncConfig)
    (cfg : YieldConfig)
    (lptAccruedA lptAccruedB : Nat) : Prop :=
  let resultA := previewSyncTrancheAccounting last currentCollateralNAV
    syncCfg { cfg with twLPTYieldShareAccruedWAD := lptAccruedA }
  let resultB := previewSyncTrancheAccounting last currentCollateralNAV
    syncCfg { cfg with twLPTYieldShareAccruedWAD := lptAccruedB }
  resultA.accounting = resultB.accounting ∧
    resultA.coverageUtilization = resultB.coverageUtilization

/-- Gross LPT NAV splits exactly and both recipients use the same conversion. -/
def LPTPremiumMintSplitSpec (input : FeeMintInput) : Prop :=
  let result := processFeesAndLiquidityPremium input
  result.retainedSTNAV = input.stEffectiveNAV -
      input.lptLiquidityPremiumGross - input.stProtocolFee ∧
    result.retainedJTNAV = input.jtEffectiveNAV - input.jtProtocolFee ∧
    result.lptLiquidityPremiumNet + input.lptProtocolFee =
      input.lptLiquidityPremiumGross ∧
    result.pooledProtocolFeeNAV =
      input.stProtocolFee + input.lptProtocolFee ∧
    result.lptOwnedSeniorTrancheSharesMinted = convertToShares
      result.lptLiquidityPremiumNet result.retainedSTNAV input.stTotalSupply ∧
    result.protocolSeniorTrancheSharesMinted = convertToShares
      result.pooledProtocolFeeNAV result.retainedSTNAV input.stTotalSupply ∧
    result.protocolJuniorTrancheSharesMinted = convertToShares
      input.jtProtocolFee result.retainedJTNAV input.jtTotalSupply ∧
    result.stTotalSupplyAfterMints = input.stTotalSupply +
      result.lptOwnedSeniorTrancheSharesMinted +
      result.protocolSeniorTrancheSharesMinted ∧
    result.jtTotalSupplyAfterMint = input.jtTotalSupply +
      result.protocolJuniorTrancheSharesMinted

def FeeMintInput.uint256Bounded (input : FeeMintInput) : Prop :=
  input.stEffectiveNAV ≤ UINT256_MAX ∧ input.stTotalSupply ≤ UINT256_MAX ∧
    input.jtEffectiveNAV ≤ UINT256_MAX ∧ input.jtTotalSupply ≤ UINT256_MAX ∧
    input.lptLiquidityPremiumGross ≤ UINT256_MAX ∧
    input.stProtocolFee ≤ UINT256_MAX ∧ input.jtProtocolFee ≤ UINT256_MAX ∧
    input.lptProtocolFee ≤ UINT256_MAX

def FeeMintResult.uint256Bounded (result : FeeMintResult) : Prop :=
  result.retainedSTNAV ≤ UINT256_MAX ∧
    result.retainedJTNAV ≤ UINT256_MAX ∧
    result.lptLiquidityPremiumNet ≤ UINT256_MAX ∧
    result.pooledProtocolFeeNAV ≤ UINT256_MAX ∧
    result.lptOwnedSeniorTrancheSharesMinted ≤ UINT256_MAX ∧
    result.protocolSeniorTrancheSharesMinted ≤ UINT256_MAX ∧
    result.protocolJuniorTrancheSharesMinted ≤ UINT256_MAX ∧
    result.stTotalSupplyAfterMints ≤ UINT256_MAX ∧
    result.jtTotalSupplyAfterMint ≤ UINT256_MAX

/-- Every eager `Math.mulDiv` evaluated by source `_convertToShares` must fit. -/
def convertToSharesSourceSafe
    (value totalValue totalSupply : Nat) : Prop :=
  let effectiveSupply := totalSupply + VIRTUAL_SHARES
  let effectiveValue := totalValue + VIRTUAL_VALUE
  let clampGate := mulDivUp effectiveSupply
    (WAD - MAX_MINT_DILUTION_WAD) MAX_MINT_DILUTION_WAD
  effectiveSupply ≤ UINT256_MAX ∧
    effectiveValue ≤ UINT256_MAX ∧
    clampGate ≤ UINT256_MAX ∧
    (clampGate > effectiveValue →
      mulDivDown effectiveSupply MAX_MINT_DILUTION_WAD
        (WAD - MAX_MINT_DILUTION_WAD) ≤ UINT256_MAX) ∧
    mulDivDown effectiveSupply value effectiveValue ≤ UINT256_MAX

def successfulMintDomain (input : FeeMintInput) : Prop :=
  let result := processFeesAndLiquidityPremium input
  input.uint256Bounded ∧
    input.stTotalSupply < UINT256_MAX ∧ input.jtTotalSupply < UINT256_MAX ∧
    input.lptProtocolFee ≤ input.lptLiquidityPremiumGross ∧
    input.stProtocolFee + input.lptProtocolFee ≤ UINT256_MAX ∧
    input.lptLiquidityPremiumGross + input.stProtocolFee ≤ input.stEffectiveNAV ∧
    input.jtProtocolFee ≤ input.jtEffectiveNAV ∧
    input.stEffectiveNAV - input.lptLiquidityPremiumGross -
      input.stProtocolFee < UINT256_MAX ∧
    input.jtEffectiveNAV - input.jtProtocolFee < UINT256_MAX ∧
    convertToSharesSourceSafe result.lptLiquidityPremiumNet
      result.retainedSTNAV input.stTotalSupply ∧
    convertToSharesSourceSafe result.pooledProtocolFeeNAV
      result.retainedSTNAV input.stTotalSupply ∧
    convertToSharesSourceSafe input.jtProtocolFee
      result.retainedJTNAV input.jtTotalSupply ∧
    result.uint256Bounded

/-- A collateral loss is absorbed by JT first and creates equal recoverable IL. -/
def STLossCoveragePrioritySpec
    (last : AccountingState)
    (loss : Nat)
    (syncCfg : SyncConfig)
    (yieldCfg : YieldConfig) : Prop :=
  let result := previewSyncTrancheAccounting
    last (last.collateralNAV - loss) syncCfg yieldCfg
  result.jtLossAbsorbed = min loss last.jtEffectiveNAV ∧
    result.residualSTLoss = loss - result.jtLossAbsorbed ∧
    result.remainingImpermanentLossBeforeTransition =
      last.jtImpermanentLoss + result.jtLossAbsorbed ∧
    result.outputs = YieldOutputs.zero

/-- The full head-source sync conserves collateral NAV on its successful domain. -/
def SyncConservationSpec
    (last : AccountingState)
    (currentCollateralNAV : Nat)
    (syncCfg : SyncConfig)
    (yieldCfg : YieldConfig) : Prop :=
  (previewSyncTrancheAccounting last currentCollateralNAV
    syncCfg yieldCfg).accounting.conserves

/-- At head, outstanding IL means the residual-gain fee/premium path was not reached. -/
def FeesRequireFullRecoverySpec
    (last : AccountingState)
    (currentCollateralNAV : Nat)
    (syncCfg : SyncConfig)
    (yieldCfg : YieldConfig) : Prop :=
  let result := previewSyncTrancheAccounting last currentCollateralNAV
    syncCfg yieldCfg
  result.remainingImpermanentLossBeforeTransition > 0 →
    result.outputs = YieldOutputs.zero

def successfulPostOpInput
    (before : AccountingState) (op : Operation) (input : PostOpInput) : Prop :=
  match op with
  | .stDeposit => before.collateralNAV < input.collateralNAV ∧
      input.lptRawNAV = before.lptRawNAV ∧ input.stSelfLiquidationBonusNAV = 0
  | .stRedemption => input.collateralNAV < before.collateralNAV ∧
      input.lptRawNAV = before.lptRawNAV ∧
      input.stSelfLiquidationBonusNAV ≤ before.collateralNAV - input.collateralNAV ∧
      input.stSelfLiquidationBonusNAV ≤ before.jtEffectiveNAV ∧
      before.collateralNAV - input.collateralNAV -
        input.stSelfLiquidationBonusNAV ≤ before.stEffectiveNAV
  | .jtDeposit => before.collateralNAV < input.collateralNAV ∧
      input.lptRawNAV = before.lptRawNAV ∧ input.stSelfLiquidationBonusNAV = 0
  | .jtRedemption => input.collateralNAV < before.collateralNAV ∧
      input.lptRawNAV = before.lptRawNAV ∧
      before.collateralNAV - input.collateralNAV ≤ before.jtEffectiveNAV ∧
      input.stSelfLiquidationBonusNAV = 0
  | .lptDeposit => input.collateralNAV = before.collateralNAV ∧
      before.lptRawNAV < input.lptRawNAV ∧ input.stSelfLiquidationBonusNAV = 0
  | .lptRedemption => input.collateralNAV = before.collateralNAV ∧
      input.lptRawNAV < before.lptRawNAV ∧ input.stSelfLiquidationBonusNAV = 0

def PostOpInput.uint256Bounded (input : PostOpInput) : Prop :=
  input.collateralNAV ≤ UINT256_MAX ∧ input.lptRawNAV ≤ UINT256_MAX ∧
    input.stSelfLiquidationBonusNAV ≤ UINT256_MAX

def PostOpResult.uint256Bounded (result : PostOpResult) : Prop :=
  result.accounting.uint256Bounded ∧ result.coverageUtilization ≤ UINT256_MAX ∧
    result.liquidityUtilization ≤ UINT256_MAX

def successfulPostOpSourceDomain
    (before : AccountingState) (op : Operation) (input : PostOpInput)
    (minCoverageWAD minLiquidityWAD : Nat) : Prop :=
  before.conserves ∧ before.uint256Bounded ∧ input.uint256Bounded ∧
    before.collateralNAV ≤ INT256_MAX ∧ input.collateralNAV ≤ INT256_MAX ∧
    before.lptRawNAV ≤ INT256_MAX ∧ input.lptRawNAV ≤ INT256_MAX ∧
    minCoverageWAD ≤ UINT64_MAX ∧ minLiquidityWAD ≤ UINT64_MAX ∧
    successfulPostOpInput before op input ∧
    (postOpSyncTrancheAccounting before op input
      minCoverageWAD minLiquidityWAD).uint256Bounded

def PostOpNoYieldSpec
    (before : AccountingState) (op : Operation) (input : PostOpInput)
    (minCoverageWAD minLiquidityWAD : Nat) : Prop :=
  (postOpSyncTrancheAccounting before op input
    minCoverageWAD minLiquidityWAD).yields = YieldOutputs.zero

def PostOpConservationSpec
    (before : AccountingState) (op : Operation) (input : PostOpInput)
    (minCoverageWAD minLiquidityWAD : Nat) : Prop :=
  (postOpSyncTrancheAccounting before op input
    minCoverageWAD minLiquidityWAD).accounting.conserves

def InnerReinvestmentCoverageNeutralSpec
    (before : ReinvestmentState)
    (requestedShares minLPTAssetsOut lptAssetsMinted minCoverageWAD : Nat)
    (venueCallSucceeded : Bool) : Prop :=
  let after := attemptLiquidityPremiumReinvestment before requestedShares
    minLPTAssetsOut lptAssetsMinted venueCallSucceeded
  after.accounting = before.accounting ∧
    coverageUtilizationWAD after.accounting.collateralNAV minCoverageWAD
      after.accounting.jtEffectiveNAV =
    coverageUtilizationWAD before.accounting.collateralNAV minCoverageWAD
      before.accounting.jtEffectiveNAV

def ReinvestmentState.uint256Bounded (state : ReinvestmentState) : Prop :=
  state.accounting.uint256Bounded ∧
    state.lptOwnedSeniorTrancheShares ≤ UINT256_MAX ∧
    state.totalLPTAssets ≤ UINT256_MAX

def successfulReinvestmentDomain
    (before : ReinvestmentState)
    (requestedShares minLPTAssetsOut lptAssetsMinted minCoverageWAD : Nat)
    (venueCallSucceeded : Bool) : Prop :=
  before.uint256Bounded ∧ requestedShares ≤ UINT256_MAX ∧
    minLPTAssetsOut ≤ UINT256_MAX ∧ lptAssetsMinted ≤ UINT256_MAX ∧
    minCoverageWAD ≤ UINT64_MAX ∧
    (venueCallSucceeded = true → minLPTAssetsOut ≤ lptAssetsMinted) ∧
    (attemptLiquidityPremiumReinvestment before requestedShares
      minLPTAssetsOut lptAssetsMinted venueCallSucceeded).uint256Bounded

/-- Regression state: a two-wei gain only repays two wei of a five-wei IL. -/
def partialRecoveryLast : AccountingState := {
  marketState := .fixedTerm
  collateralNAV := 1_200_000_000_000_000_000_000
  lptRawNAV := 100_000_000_000_000_000_000
  stEffectiveNAV := 1_000_000_000_000_000_000_005
  jtEffectiveNAV := 199_999_999_999_999_999_995
  jtImpermanentLoss := 5
}

def partialRecoveryYieldConfig : YieldConfig := {
  elapsedSinceLastPremiumPayments := 1
  twJTYieldShareAccruedWAD := 100_000_000_000_000_000
  twLPTYieldShareAccruedWAD := 50_000_000_000_000_000
  stProtocolFeeWAD := 100_000_000_000_000_000
  jtProtocolFeeWAD := 100_000_000_000_000_000
  jtYieldShareProtocolFeeWAD := 100_000_000_000_000_000
  lptYieldShareProtocolFeeWAD := 100_000_000_000_000_000
}

def partialRecoverySyncConfig : SyncConfig := {
  dustTolerance := 0
  minCoverageWAD := 100_000_000_000_000_000
  minLiquidityWAD := 100_000_000_000_000_000
  coverageLiquidationUtilizationWAD := 2 * WAD
  fixedTermDurationZero := false
  fixedTermExpired := false
  fixedTermGracePeriodActive := false
}

def PartialRecoveryNoFeeRegressionSpec : Prop :=
  let result := previewSyncTrancheAccounting partialRecoveryLast
    (partialRecoveryLast.collateralNAV + 2) partialRecoverySyncConfig
    partialRecoveryYieldConfig
  result.accounting.conserves ∧
    result.jtImpermanentLossRepaid = 2 ∧
    result.remainingImpermanentLossBeforeTransition = 3 ∧
    result.residualGainAfterRepayment = 0 ∧
    result.outputs = YieldOutputs.zero

end Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority
