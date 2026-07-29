import Verity

/-!
# Royco Day LT liquidity-premium priority model

Source: `roycoprotocol/royco-day` at
`3401dd0f6b010cf920b49c6c26e6704fa7c769b7`.

This is a source-structured protocol slice of Royco Day's accountant, fee mint,
post-operation checkpoint, utilization, and inner Balancer reinvestment logic.
It is not a Royco Dawn model.

Simplifications and scope:

1. `NAV_UNIT`, `TRANCHE_UNIT`, and `uint256` are represented by `Nat`. Royco's
   full-precision floor and ceiling `Math.mulDiv` modes are exact natural
   multiplication followed by floor or ceiling division. Specs state the
   successful checked-arithmetic domain where needed.
2. Signed raw-NAV attribution is represented by its two source outputs,
   `deltaJTEffectiveNAV` and `deltaSTEffectiveNAV`, while current ST/JT/LT raw
   NAVs are explicit inputs. The claim-decomposition routine that derives those
   deltas remains outside this slice.
3. Runtime external YDM calls and timestamp updates are supplied as the elapsed
   premium window and the two already-capped time-weighted accumulators. The
   source's single floor over `residual * accumulator / (elapsed * WAD)` and
   accumulated-window cap are retained. The source same-block branch is encoded
   exactly with `elapsed = 1` and each capped instantaneous share as its
   accumulator.
4. Market-state selection is represented by the resulting state and the source
   branch's explicit IL-erasure flag. The exact fixed-term behavior that zeroes
   all fee and premium outputs is retained.
5. ERC20 callbacks and recipient balances are not modeled. The fee leg retains
   the exact `_convertToShares` bootstrap, zero-value, dilution-clamp, and floor
   branches, both recipient share amounts, and post-mint total supply.
6. `postOpSyncTrancheAccountingUnchecked` is intentionally only the accountant
   transition when `_enforceCoverageAndLiquidityRequirements == false`. The
   public enforcement branch is not claimed. Exact resulting coverage and
   liquidity utilizations are still returned.
7. `attemptLiquidityPremiumReinvestment` starts after the public wrapper's
   compulsory pre-op sync. Oracle/slippage valuation is represented by the
   already-computed `minLTAssetsOut`; the source cap, zero-floor no-op, failed
   call rollback, and successful LT asset-ledger update are retained.
-/

namespace Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority

def WAD : Nat := 1_000_000_000_000_000_000

def MAX_MINT_DILUTION_WAD : Nat := WAD - 1_000_000

def UINT256_MAX : Nat := 2 ^ 256 - 1

/-- Largest nonnegative NAV value accepted by the source's checked `toInt256`. -/
def INT256_MAX : Nat := 2 ^ 255 - 1

def mulDivDown (x y denominator : Nat) : Nat := x * y / denominator

def mulDivUp (x y denominator : Nat) : Nat :=
  (x * y + denominator - 1) / denominator

inductive MarketState where
  | perpetual
  | fixedTerm
  deriving Repr, DecidableEq

inductive SignedDelta where
  | loss (amount : Nat)
  | flat
  | gain (amount : Nat)
  deriving Repr, DecidableEq

def SignedDelta.magnitude : SignedDelta → Nat
  | .loss amount | .gain amount => amount
  | .flat => 0

structure RawNAVs where
  stRawNAV : Nat
  jtRawNAV : Nat
  ltRawNAV : Nat
  deriving Repr, DecidableEq

structure AccountingState where
  raw : RawNAVs
  stEffectiveNAV : Nat
  jtEffectiveNAV : Nat
  jtCoverageImpermanentLoss : Nat
  deriving Repr, DecidableEq

def AccountingState.conserves (s : AccountingState) : Prop :=
  s.raw.stRawNAV + s.raw.jtRawNAV = s.stEffectiveNAV + s.jtEffectiveNAV

def coverageUtilizationWAD
    (raw : RawNAVs)
    (minCoverageWAD jtEffectiveNAV : Nat) : Nat :=
  let totalCoveredExposure := raw.stRawNAV + raw.jtRawNAV
  if minCoverageWAD = 0 then
    0
  else if totalCoveredExposure = 0 then
    0
  else if jtEffectiveNAV = 0 then
    UINT256_MAX
  else
    mulDivUp totalCoveredExposure minCoverageWAD jtEffectiveNAV

def liquidityUtilizationWAD
    (raw : RawNAVs)
    (minLiquidityWAD stEffectiveNAV : Nat) : Nat :=
  if stEffectiveNAV = 0 ∨ minLiquidityWAD = 0 then
    0
  else if raw.ltRawNAV = 0 then
    UINT256_MAX
  else
    mulDivUp stEffectiveNAV minLiquidityWAD raw.ltRawNAV

structure YieldConfig where
  elapsedSinceLastPremiumPayments : Nat
  twJTYieldShareAccruedWAD : Nat
  twLTYieldShareAccruedWAD : Nat
  stProtocolFeeWAD : Nat
  jtProtocolFeeWAD : Nat
  jtYieldShareProtocolFeeWAD : Nat
  ltYieldShareProtocolFeeWAD : Nat
  deriving Repr, DecidableEq

def YieldConfig.valid (cfg : YieldConfig) : Prop :=
  0 < cfg.elapsedSinceLastPremiumPayments ∧
    cfg.twJTYieldShareAccruedWAD + cfg.twLTYieldShareAccruedWAD ≤
      cfg.elapsedSinceLastPremiumPayments * WAD ∧
    cfg.stProtocolFeeWAD ≤ WAD ∧
    cfg.jtProtocolFeeWAD ≤ WAD ∧
    cfg.jtYieldShareProtocolFeeWAD ≤ WAD ∧
    cfg.ltYieldShareProtocolFeeWAD ≤ WAD

structure SyncConfig where
  effectiveNAVDustTolerance : Nat
  minCoverageWAD : Nat
  minLiquidityWAD : Nat
  resultingMarketState : MarketState
  eraseCoverageIL : Bool
  deriving Repr, DecidableEq

structure YieldOutputs where
  ltLiquidityPremium : Nat
  stProtocolFee : Nat
  jtProtocolFee : Nat
  ltProtocolFee : Nat
  deriving Repr, DecidableEq

def YieldOutputs.zero : YieldOutputs := {
  ltLiquidityPremium := 0
  stProtocolFee := 0
  jtProtocolFee := 0
  ltProtocolFee := 0
}

structure JTStepResult where
  jtEffectiveNAV : Nat
  jtNetGain : Nat
  jtProtocolFee : Nat
  deriving Repr, DecidableEq

def applyJTEffectiveDelta
    (jtEffectiveNAV : Nat)
    (delta : SignedDelta)
    (dust jtProtocolFeeWAD : Nat) : JTStepResult :=
  match delta with
  | .loss loss => {
      jtEffectiveNAV := jtEffectiveNAV - loss
      jtNetGain := 0
      jtProtocolFee := 0
    }
  | .flat => {
      jtEffectiveNAV := jtEffectiveNAV
      jtNetGain := 0
      jtProtocolFee := 0
    }
  | .gain gain => {
      jtEffectiveNAV := jtEffectiveNAV + gain
      jtNetGain := gain
      jtProtocolFee :=
        if gain > dust then mulDivDown gain jtProtocolFeeWAD WAD else 0
    }

def coverageRecovery (stGain coverageIL : Nat) : Nat := min stGain coverageIL

def residualSeniorYield (stGain coverageIL : Nat) : Nat :=
  stGain - coverageRecovery stGain coverageIL

def grossPremium
    (residualYield timeWeightedYieldShareAccruedWAD
      elapsedSinceLastPremiumPayments : Nat) : Nat :=
  mulDivDown residualYield timeWeightedYieldShareAccruedWAD
    (elapsedSinceLastPremiumPayments * WAD)

structure SyncResult where
  accounting : AccountingState
  outputs : YieldOutputs
  recoveredCoverageIL : Nat
  remainingCoverageILBeforeTransition : Nat
  residualSeniorYield : Nat
  jtRiskPremiumGross : Nat
  jtYieldShareProtocolFee : Nat
  priorJTPnlProtocolFee : Nat
  jtCoverageApplied : Nat
  residualSeniorLoss : Nat
  coverageUtilization : Nat
  liquidityUtilization : Nat
  resultingMarketState : MarketState
  deriving Repr, DecidableEq

def finalizeSyncResult
    (provisional : SyncResult)
    (cfg : SyncConfig) : SyncResult :=
  let outputs :=
    if cfg.resultingMarketState = .fixedTerm then YieldOutputs.zero
    else provisional.outputs
  let accounting :=
    if cfg.eraseCoverageIL then
      { provisional.accounting with jtCoverageImpermanentLoss := 0 }
    else
      provisional.accounting
  {
    provisional with
    accounting := accounting
    outputs := outputs
    resultingMarketState := cfg.resultingMarketState
  }

def handleSTGain
    (last : AccountingState)
    (currentRaw : RawNAVs)
    (jtStep : JTStepResult)
    (stGain : Nat)
    (syncCfg : SyncConfig)
    (yieldCfg : YieldConfig) : SyncResult :=
  let recovered := coverageRecovery stGain last.jtCoverageImpermanentLoss
  let remainingIL := last.jtCoverageImpermanentLoss - recovered
  let residual := stGain - recovered
  let jtPremium := grossPremium residual yieldCfg.twJTYieldShareAccruedWAD
    yieldCfg.elapsedSinceLastPremiumPayments
  let ltPremium := grossPremium residual yieldCfg.twLTYieldShareAccruedWAD
    yieldCfg.elapsedSinceLastPremiumPayments
  let premiumsPaid := residual > syncCfg.effectiveNAVDustTolerance
  let stFeeBase := residual - jtPremium - ltPremium
  let stFee :=
    if premiumsPaid then mulDivDown stFeeBase yieldCfg.stProtocolFeeWAD WAD else 0
  let jtYieldFee :=
    if premiumsPaid then
      mulDivDown jtPremium yieldCfg.jtYieldShareProtocolFeeWAD WAD
    else 0
  let ltYieldFee :=
    if premiumsPaid then
      mulDivDown ltPremium yieldCfg.ltYieldShareProtocolFeeWAD WAD
    else 0
  let accounting : AccountingState := {
    raw := currentRaw
    stEffectiveNAV := last.stEffectiveNAV + residual - jtPremium
    jtEffectiveNAV := jtStep.jtEffectiveNAV + recovered + jtPremium
    jtCoverageImpermanentLoss := remainingIL
  }
  let provisional : SyncResult := {
    accounting := accounting
    outputs := {
      ltLiquidityPremium := ltPremium
      stProtocolFee := stFee
      jtProtocolFee := jtStep.jtProtocolFee + jtYieldFee
      ltProtocolFee := ltYieldFee
    }
    recoveredCoverageIL := recovered
    remainingCoverageILBeforeTransition := remainingIL
    residualSeniorYield := residual
    jtRiskPremiumGross := jtPremium
    jtYieldShareProtocolFee := jtYieldFee
    priorJTPnlProtocolFee := jtStep.jtProtocolFee
    jtCoverageApplied := 0
    residualSeniorLoss := 0
    coverageUtilization :=
      coverageUtilizationWAD currentRaw syncCfg.minCoverageWAD accounting.jtEffectiveNAV
    liquidityUtilization :=
      liquidityUtilizationWAD currentRaw syncCfg.minLiquidityWAD accounting.stEffectiveNAV
    resultingMarketState := syncCfg.resultingMarketState
  }
  finalizeSyncResult provisional syncCfg

def handleSTLoss
    (last : AccountingState)
    (currentRaw : RawNAVs)
    (jtStep : JTStepResult)
    (stLoss : Nat)
    (syncCfg : SyncConfig)
    (yieldCfg : YieldConfig) : SyncResult :=
  let coverageApplied := min stLoss jtStep.jtEffectiveNAV
  let residualLoss := stLoss - coverageApplied
  let jtNetGainAfterCoverage := jtStep.jtNetGain - coverageApplied
  let recomputedJTFee :=
    if jtStep.jtProtocolFee = 0 then
      0
    else if jtNetGainAfterCoverage > syncCfg.effectiveNAVDustTolerance then
      mulDivDown jtNetGainAfterCoverage yieldCfg.jtProtocolFeeWAD WAD
    else 0
  let accounting : AccountingState := {
    raw := currentRaw
    stEffectiveNAV := last.stEffectiveNAV - residualLoss
    jtEffectiveNAV := jtStep.jtEffectiveNAV - coverageApplied
    jtCoverageImpermanentLoss :=
      last.jtCoverageImpermanentLoss + coverageApplied
  }
  let provisional : SyncResult := {
    accounting := accounting
    outputs := {
      ltLiquidityPremium := 0
      stProtocolFee := 0
      jtProtocolFee := recomputedJTFee
      ltProtocolFee := 0
    }
    recoveredCoverageIL := 0
    remainingCoverageILBeforeTransition := accounting.jtCoverageImpermanentLoss
    residualSeniorYield := 0
    jtRiskPremiumGross := 0
    jtYieldShareProtocolFee := 0
    priorJTPnlProtocolFee := jtStep.jtProtocolFee
    jtCoverageApplied := coverageApplied
    residualSeniorLoss := residualLoss
    coverageUtilization :=
      coverageUtilizationWAD currentRaw syncCfg.minCoverageWAD accounting.jtEffectiveNAV
    liquidityUtilization :=
      liquidityUtilizationWAD currentRaw syncCfg.minLiquidityWAD accounting.stEffectiveNAV
    resultingMarketState := syncCfg.resultingMarketState
  }
  finalizeSyncResult provisional syncCfg

def handleSTFlat
    (last : AccountingState)
    (currentRaw : RawNAVs)
    (jtStep : JTStepResult)
    (syncCfg : SyncConfig) : SyncResult :=
  let accounting : AccountingState := {
    raw := currentRaw
    stEffectiveNAV := last.stEffectiveNAV
    jtEffectiveNAV := jtStep.jtEffectiveNAV
    jtCoverageImpermanentLoss := last.jtCoverageImpermanentLoss
  }
  let provisional : SyncResult := {
    accounting := accounting
    outputs := {
      ltLiquidityPremium := 0
      stProtocolFee := 0
      jtProtocolFee := jtStep.jtProtocolFee
      ltProtocolFee := 0
    }
    recoveredCoverageIL := 0
    remainingCoverageILBeforeTransition := accounting.jtCoverageImpermanentLoss
    residualSeniorYield := 0
    jtRiskPremiumGross := 0
    jtYieldShareProtocolFee := 0
    priorJTPnlProtocolFee := jtStep.jtProtocolFee
    jtCoverageApplied := 0
    residualSeniorLoss := 0
    coverageUtilization :=
      coverageUtilizationWAD currentRaw syncCfg.minCoverageWAD accounting.jtEffectiveNAV
    liquidityUtilization :=
      liquidityUtilizationWAD currentRaw syncCfg.minLiquidityWAD accounting.stEffectiveNAV
    resultingMarketState := syncCfg.resultingMarketState
  }
  finalizeSyncResult provisional syncCfg

/-- Source-order pre-op sync: JT PnL first, then ST loss/recovery/premiums. -/
def previewSyncTrancheAccounting
    (last : AccountingState)
    (currentRaw : RawNAVs)
    (deltaJTEffectiveNAV deltaSTEffectiveNAV : SignedDelta)
    (syncCfg : SyncConfig)
    (yieldCfg : YieldConfig) : SyncResult :=
  let jtStep := applyJTEffectiveDelta
    last.jtEffectiveNAV deltaJTEffectiveNAV
    syncCfg.effectiveNAVDustTolerance yieldCfg.jtProtocolFeeWAD
  match deltaSTEffectiveNAV with
  | .loss loss => handleSTLoss last currentRaw jtStep loss syncCfg yieldCfg
  | .flat => handleSTFlat last currentRaw jtStep syncCfg
  | .gain gain => handleSTGain last currentRaw jtStep gain syncCfg yieldCfg

/-- Exact source share conversion, including bootstrap, zero-value, and clamp. -/
def convertToShares (value totalValue totalSupply : Nat) : Nat :=
  if totalSupply = 0 then
    value
  else
    let denominator := if totalValue = 0 then 1 else totalValue
    if mulDivUp value (WAD - MAX_MINT_DILUTION_WAD) MAX_MINT_DILUTION_WAD > denominator then
      mulDivDown totalSupply MAX_MINT_DILUTION_WAD (WAD - MAX_MINT_DILUTION_WAD)
    else
      mulDivDown totalSupply value denominator

structure FeeMintInput where
  stEffectiveNAV : Nat
  stTotalSupply : Nat
  ltLiquidityPremiumGross : Nat
  stProtocolFee : Nat
  ltYieldShareProtocolFee : Nat
  deriving Repr, DecidableEq

structure FeeMintResult where
  retainedSTNAV : Nat
  ltLiquidityPremiumNet : Nat
  pooledProtocolFeeNAV : Nat
  ltOwnedSeniorTrancheSharesMinted : Nat
  protocolSeniorTrancheSharesMinted : Nat
  stTotalSupplyAfterMints : Nat
  deriving Repr, DecidableEq

def processFeesAndLiquidityPremium (input : FeeMintInput) : FeeMintResult :=
  let retained :=
    input.stEffectiveNAV - input.ltLiquidityPremiumGross - input.stProtocolFee
  let ltNet :=
    input.ltLiquidityPremiumGross - input.ltYieldShareProtocolFee
  let pooledFee := input.stProtocolFee + input.ltYieldShareProtocolFee
  let premiumShares := convertToShares ltNet retained input.stTotalSupply
  let protocolShares := convertToShares pooledFee retained input.stTotalSupply
  {
    retainedSTNAV := retained
    ltLiquidityPremiumNet := ltNet
    pooledProtocolFeeNAV := pooledFee
    ltOwnedSeniorTrancheSharesMinted := premiumShares
    protocolSeniorTrancheSharesMinted := protocolShares
    stTotalSupplyAfterMints := input.stTotalSupply + premiumShares + protocolShares
  }

inductive Operation where
  | stDeposit
  | jtDeposit
  | ltDeposit
  | stRedeem
  | jtRedeem
  | ltRedeem
  deriving Repr, DecidableEq

structure OperationAmounts where
  stAmount : Nat
  jtAmount : Nat
  ltRawNAVAfter : Nat
  stSelfLiquidationBonusNAV : Nat
  deriving Repr, DecidableEq

structure PostOpResult where
  accounting : AccountingState
  yields : YieldOutputs
  coverageUtilization : Nat
  liquidityUtilization : Nat
  deriving Repr, DecidableEq

/--
Exact accountant transition for the source branch where requirement enforcement
is disabled. The public enforcing branch is intentionally outside this theorem.
-/
def postOpSyncTrancheAccountingUnchecked
    (before : AccountingState)
    (op : Operation)
    (amounts : OperationAmounts)
    (minCoverageWAD minLiquidityWAD : Nat) : PostOpResult :=
  let totalRedemption := amounts.stAmount + amounts.jtAmount
  let accounting : AccountingState := match op with
    | .stDeposit => {
        before with
        raw := {
          before.raw with
          stRawNAV := before.raw.stRawNAV + amounts.stAmount
        }
        stEffectiveNAV := before.stEffectiveNAV + amounts.stAmount
      }
    | .jtDeposit => {
        before with
        raw := {
          before.raw with
          jtRawNAV := before.raw.jtRawNAV + amounts.jtAmount
        }
        jtEffectiveNAV := before.jtEffectiveNAV + amounts.jtAmount
      }
    | .ltDeposit => {
        before with
        raw := {
          stRawNAV := before.raw.stRawNAV + amounts.stAmount
          jtRawNAV := before.raw.jtRawNAV
          ltRawNAV := amounts.ltRawNAVAfter
        }
        stEffectiveNAV := before.stEffectiveNAV + amounts.stAmount
      }
    | .stRedeem => {
        before with
        raw := {
          before.raw with
          stRawNAV := before.raw.stRawNAV - amounts.stAmount
          jtRawNAV := before.raw.jtRawNAV - amounts.jtAmount
        }
        stEffectiveNAV :=
          before.stEffectiveNAV -
            (totalRedemption - amounts.stSelfLiquidationBonusNAV)
        jtEffectiveNAV :=
          before.jtEffectiveNAV - amounts.stSelfLiquidationBonusNAV
      }
    | .ltRedeem => {
        before with
        raw := {
          stRawNAV := before.raw.stRawNAV - amounts.stAmount
          jtRawNAV := before.raw.jtRawNAV - amounts.jtAmount
          ltRawNAV := amounts.ltRawNAVAfter
        }
        stEffectiveNAV :=
          before.stEffectiveNAV -
            (totalRedemption - amounts.stSelfLiquidationBonusNAV)
        jtEffectiveNAV :=
          before.jtEffectiveNAV - amounts.stSelfLiquidationBonusNAV
      }
    | .jtRedeem =>
        let jtEffectiveAfter := before.jtEffectiveNAV - totalRedemption
        {
          before with
          raw := {
            before.raw with
            stRawNAV := before.raw.stRawNAV - amounts.stAmount
            jtRawNAV := before.raw.jtRawNAV - amounts.jtAmount
          }
          jtEffectiveNAV := jtEffectiveAfter
          jtCoverageImpermanentLoss :=
            if before.jtCoverageImpermanentLoss = 0 then 0
            else mulDivDown
              before.jtCoverageImpermanentLoss
              jtEffectiveAfter
              before.jtEffectiveNAV
        }
  {
    accounting := accounting
    yields := YieldOutputs.zero
    coverageUtilization :=
      coverageUtilizationWAD accounting.raw minCoverageWAD accounting.jtEffectiveNAV
    liquidityUtilization :=
      liquidityUtilizationWAD accounting.raw minLiquidityWAD accounting.stEffectiveNAV
  }

structure ReinvestmentState where
  accounting : AccountingState
  ltOwnedSeniorTrancheShares : Nat
  ltOwnedYieldBearingAssets : Nat
  deriving Repr, DecidableEq

/-- Exact inner-leg state shape after oracle/slippage valuation. -/
def attemptLiquidityPremiumReinvestment
    (before : ReinvestmentState)
    (requestedShares minLTAssetsOut ltAssetsMinted : Nat)
    (venueCallSucceeded : Bool) : ReinvestmentState :=
  let sharesToReinvest := min requestedShares before.ltOwnedSeniorTrancheShares
  if sharesToReinvest = 0 then
    before
  else if minLTAssetsOut = 0 then
    before
  else if venueCallSucceeded then
    {
      before with
      ltOwnedSeniorTrancheShares :=
        before.ltOwnedSeniorTrancheShares - sharesToReinvest
      ltOwnedYieldBearingAssets :=
        before.ltOwnedYieldBearingAssets + ltAssetsMinted
    }
  else
    before

end Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority
