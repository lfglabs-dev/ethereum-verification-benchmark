import Verity

/-!
# Royco Day LPT liquidity-premium priority model

Source: `roycoprotocol/royco-day` at
`13f528821ccd233588c4bd63da9024fe454564ab` (PR #20 head), based on
`23b1c993060e7a9db9618de53c36cef8632c0596` (`audit/remediations`).

This source-structured slice follows the head accountant waterfall, fee mint,
six post-operation shapes, utilization, virtual-share valuation, and inner
Balancer reinvestment state update. The historical module/case identifier keeps
`LT` for benchmark compatibility; all modeled source identifiers use `LPT`.

Simplifications and refinement boundaries:

1. Solidity `NAV_UNIT`, `TRANCHE_UNIT`, `uint256`, `uint128`, and timestamps are
   represented by `Nat`. Source-facing specs state the successful uint256,
   uint128, and checked-int256 domains. `mulDivDown`/`mulDivUp` retain exact
   full-precision floor/ceiling semantics.
2. External collateral/LPT oracle reads and YDM calls are inputs: current NAVs,
   elapsed premium window, and already-capped time-weighted accumulators. The
   source's same-block branch is represented by `elapsed = 1` and instantaneous
   capped shares as the accumulators.
3. Fixed-term expiry is a supplied boolean. The transition itself is modeled:
   duration zero, JT wipe, IL at/below dust, expiry, or liquidation-utilization
   breach forces `PERPETUAL` and clears IL; otherwise the result is `FIXED_TERM`.
   Timestamp writes and events are omitted.
4. ERC20 callbacks and balances are omitted. Fee mint sizing preserves retained
   senior NAV, virtual shares/value, collapsed-price clamp, floor rounding,
   recipient quantities, and post-mint supply.
5. Post-op coverage/liquidity enforcement lives in kernel logic. This slice
   models the accountant's six accepted operation shapes and exposes the exact
   utilizations on which the kernel gates. Multi-asset cache choreography is
   outside the pure transition and is not claimed as verified.
6. Reinvestment starts after sync and slippage valuation. `minLPTAssetsOut` is
   supplied; the cap, zero-floor no-op, failed inner-call rollback, and successful
   `lptOwnedSeniorTrancheShares`/`totalLPTAssets` updates are retained. Token and
   Balancer callback effects are outside the state slice.
-/

namespace Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority

def WAD : Nat := 1_000_000_000_000_000_000

def MAX_MINT_DILUTION_WAD : Nat := WAD - 1_000_000

def VIRTUAL_SHARES : Nat := 1

def VIRTUAL_VALUE : Nat := 1

def UINT128_MAX : Nat := 2 ^ 128 - 1

def UINT64_MAX : Nat := 2 ^ 64 - 1

def UINT256_MAX : Nat := 2 ^ 256 - 1

def INT256_MAX : Nat := 2 ^ 255 - 1

def mulDivDown (x y denominator : Nat) : Nat := x * y / denominator

def mulDivUp (x y denominator : Nat) : Nat :=
  (x * y + denominator - 1) / denominator

inductive MarketState where
  | perpetual
  | fixedTerm
  deriving Repr, DecidableEq

structure AccountingState where
  marketState : MarketState
  collateralNAV : Nat
  lptRawNAV : Nat
  stEffectiveNAV : Nat
  jtEffectiveNAV : Nat
  jtImpermanentLoss : Nat
  deriving Repr, DecidableEq

def AccountingState.conserves (s : AccountingState) : Prop :=
  s.collateralNAV = s.stEffectiveNAV + s.jtEffectiveNAV

def coverageUtilizationWAD
    (collateralNAV minCoverageWAD jtEffectiveNAV : Nat) : Nat :=
  if minCoverageWAD = 0 ∨ collateralNAV = 0 then
    0
  else if jtEffectiveNAV = 0 then
    UINT256_MAX
  else
    mulDivUp collateralNAV minCoverageWAD jtEffectiveNAV

def liquidityUtilizationWAD
    (stEffectiveNAV minLiquidityWAD lptRawNAV : Nat) : Nat :=
  if stEffectiveNAV = 0 ∨ minLiquidityWAD = 0 then
    0
  else if lptRawNAV = 0 then
    UINT256_MAX
  else
    mulDivUp stEffectiveNAV minLiquidityWAD lptRawNAV

structure YieldConfig where
  elapsedSinceLastPremiumPayments : Nat
  twJTYieldShareAccruedWAD : Nat
  twLPTYieldShareAccruedWAD : Nat
  stProtocolFeeWAD : Nat
  jtProtocolFeeWAD : Nat
  jtYieldShareProtocolFeeWAD : Nat
  lptYieldShareProtocolFeeWAD : Nat
  deriving Repr, DecidableEq

def YieldConfig.valid (cfg : YieldConfig) : Prop :=
  0 < cfg.elapsedSinceLastPremiumPayments ∧
    cfg.twJTYieldShareAccruedWAD + cfg.twLPTYieldShareAccruedWAD ≤
      cfg.elapsedSinceLastPremiumPayments * WAD ∧
    cfg.stProtocolFeeWAD ≤ WAD ∧
    cfg.jtProtocolFeeWAD ≤ WAD ∧
    cfg.jtYieldShareProtocolFeeWAD ≤ WAD ∧
    cfg.lptYieldShareProtocolFeeWAD ≤ WAD

structure SyncConfig where
  dustTolerance : Nat
  minCoverageWAD : Nat
  minLiquidityWAD : Nat
  coverageLiquidationUtilizationWAD : Nat
  fixedTermDurationZero : Bool
  fixedTermExpired : Bool
  deriving Repr, DecidableEq

structure YieldOutputs where
  lptLiquidityPremium : Nat
  stProtocolFee : Nat
  jtProtocolFee : Nat
  lptProtocolFee : Nat
  deriving Repr, DecidableEq

def YieldOutputs.zero : YieldOutputs := {
  lptLiquidityPremium := 0
  stProtocolFee := 0
  jtProtocolFee := 0
  lptProtocolFee := 0
}

def grossPremium
    (stGain timeWeightedYieldShareAccruedWAD
      elapsedSinceLastPremiumPayments : Nat) : Nat :=
  mulDivDown stGain timeWeightedYieldShareAccruedWAD
    (elapsedSinceLastPremiumPayments * WAD)

structure SyncResult where
  accounting : AccountingState
  outputs : YieldOutputs
  jtImpermanentLossRepaid : Nat
  remainingImpermanentLossBeforeTransition : Nat
  residualGainAfterRepayment : Nat
  stGain : Nat
  jtGain : Nat
  jtRiskPremiumGross : Nat
  jtYieldShareProtocolFee : Nat
  jtLossAbsorbed : Nat
  residualSTLoss : Nat
  coverageUtilization : Nat
  liquidityUtilization : Nat
  deriving Repr, DecidableEq

def shouldBePerpetual (state : AccountingState) (cfg : SyncConfig) : Bool :=
  cfg.fixedTermDurationZero ||
    decide (state.jtEffectiveNAV = 0) ||
    decide (state.jtImpermanentLoss ≤ cfg.dustTolerance) ||
    (decide (state.marketState = .fixedTerm) && cfg.fixedTermExpired) ||
    decide (coverageUtilizationWAD state.collateralNAV cfg.minCoverageWAD
      state.jtEffectiveNAV ≥ cfg.coverageLiquidationUtilizationWAD)

def applyMarketTransition
    (provisional : SyncResult) (cfg : SyncConfig) : SyncResult :=
  let transitionedAccounting :=
    if shouldBePerpetual provisional.accounting cfg then
      {
        provisional.accounting with
        marketState := .perpetual
        jtImpermanentLoss := 0
      }
    else
      { provisional.accounting with marketState := .fixedTerm }
  { provisional with accounting := transitionedAccounting }

def finalizeSyncResult
    (accounting : AccountingState)
    (outputs : YieldOutputs)
    (repaid remaining residualGain stGain jtGain jtRiskPremium
      jtYieldFee jtLoss residualSTLoss : Nat)
    (cfg : SyncConfig) : SyncResult :=
  applyMarketTransition {
    accounting := accounting
    outputs := outputs
    jtImpermanentLossRepaid := repaid
    remainingImpermanentLossBeforeTransition := remaining
    residualGainAfterRepayment := residualGain
    stGain := stGain
    jtGain := jtGain
    jtRiskPremiumGross := jtRiskPremium
    jtYieldShareProtocolFee := jtYieldFee
    jtLossAbsorbed := jtLoss
    residualSTLoss := residualSTLoss
    coverageUtilization := coverageUtilizationWAD
      accounting.collateralNAV cfg.minCoverageWAD accounting.jtEffectiveNAV
    liquidityUtilization := liquidityUtilizationWAD
      accounting.stEffectiveNAV cfg.minLiquidityWAD accounting.lptRawNAV
  } cfg

/-- The pure accountant preview leaves the kernel-computed LPT mark and liquidity
utilization at zero. `AccountingSyncLogic` fills them after the preview returns. -/
def finalizePreviewSyncResult
    (accounting : AccountingState)
    (outputs : YieldOutputs)
    (repaid remaining residualGain stGain jtGain jtRiskPremium jtYieldFee
      jtLoss residualSTLoss : Nat)
    (cfg : SyncConfig) : SyncResult :=
  { finalizeSyncResult accounting outputs repaid remaining residualGain stGain
      jtGain jtRiskPremium jtYieldFee jtLoss residualSTLoss cfg with
    liquidityUtilization := 0 }

/-- Head-source collateral loss waterfall: JT absorbs first, then ST. -/
def handleCollateralLoss
    (last : AccountingState)
    (currentCollateralNAV loss : Nat)
    (cfg : SyncConfig) : SyncResult :=
  let jtLoss := min loss last.jtEffectiveNAV
  let residualLoss := loss - jtLoss
  let accounting : AccountingState := {
    last with
    collateralNAV := currentCollateralNAV
    lptRawNAV := 0
    stEffectiveNAV := last.stEffectiveNAV - residualLoss
    jtEffectiveNAV := last.jtEffectiveNAV - jtLoss
    jtImpermanentLoss := last.jtImpermanentLoss + jtLoss
  }
  finalizePreviewSyncResult accounting YieldOutputs.zero
    0 accounting.jtImpermanentLoss 0 0 0 0 0 jtLoss residualLoss cfg

/-- ST's floor-rounded share of collateral gain after global IL repayment. -/
def residualSTGain
    (last : AccountingState) (currentCollateralNAV : Nat) : Nat :=
  let gain := currentCollateralNAV - last.collateralNAV
  let repaid := min gain last.jtImpermanentLoss
  let residualGain := gain - repaid
  let restoredCollateralNAV := last.collateralNAV + repaid
  if restoredCollateralNAV = 0 then residualGain
  else mulDivDown residualGain last.stEffectiveNAV restoredCollateralNAV

/-- Head-source collateral gain waterfall: repay JT IL, then split and pay yield shares. -/
def handleCollateralGain
    (last : AccountingState)
    (currentCollateralNAV gain : Nat)
    (cfg : SyncConfig)
    (yieldCfg : YieldConfig) : SyncResult :=
  let repaid := min gain last.jtImpermanentLoss
  let remainingIL := last.jtImpermanentLoss - repaid
  let residualGain := gain - repaid
  let stGain := residualSTGain last currentCollateralNAV
  let jtGain := residualGain - stGain
  let jtPnlFee :=
    if jtGain > cfg.dustTolerance then
      mulDivDown jtGain yieldCfg.jtProtocolFeeWAD WAD
    else 0
  let premiumsPaid := stGain > cfg.dustTolerance
  let jtRiskPremium := grossPremium stGain
    yieldCfg.twJTYieldShareAccruedWAD
    yieldCfg.elapsedSinceLastPremiumPayments
  let lptLiquidityPremium := grossPremium stGain
    yieldCfg.twLPTYieldShareAccruedWAD
    yieldCfg.elapsedSinceLastPremiumPayments
  let jtYieldFee :=
    if premiumsPaid then
      mulDivDown jtRiskPremium yieldCfg.jtYieldShareProtocolFeeWAD WAD
    else 0
  let lptFee :=
    if premiumsPaid then
      mulDivDown lptLiquidityPremium yieldCfg.lptYieldShareProtocolFeeWAD WAD
    else 0
  let stFeeBase := stGain - jtRiskPremium - lptLiquidityPremium
  let stFee :=
    if premiumsPaid then
      mulDivDown stFeeBase yieldCfg.stProtocolFeeWAD WAD
    else 0
  let accounting : AccountingState := {
    last with
    collateralNAV := currentCollateralNAV
    lptRawNAV := 0
    stEffectiveNAV := last.stEffectiveNAV + stGain - jtRiskPremium
    jtEffectiveNAV := last.jtEffectiveNAV + repaid + jtGain + jtRiskPremium
    jtImpermanentLoss := remainingIL
  }
  finalizePreviewSyncResult accounting {
      lptLiquidityPremium := lptLiquidityPremium
      stProtocolFee := stFee
      jtProtocolFee := jtPnlFee + jtYieldFee
      lptProtocolFee := lptFee
    }
    repaid remainingIL residualGain stGain jtGain jtRiskPremium
    jtYieldFee 0 0 cfg

/-- Exact head ordering selected by the collateral NAV delta. -/
def previewSyncTrancheAccounting
    (last : AccountingState)
    (currentCollateralNAV : Nat)
    (cfg : SyncConfig)
    (yieldCfg : YieldConfig) : SyncResult :=
  if currentCollateralNAV < last.collateralNAV then
    handleCollateralLoss last currentCollateralNAV
      (last.collateralNAV - currentCollateralNAV) cfg
  else if last.collateralNAV < currentCollateralNAV then
    handleCollateralGain last currentCollateralNAV
      (currentCollateralNAV - last.collateralNAV) cfg yieldCfg
  else
    finalizePreviewSyncResult
      { last with lptRawNAV := 0 }
      YieldOutputs.zero 0 last.jtImpermanentLoss 0 0 0 0 0 0 0 cfg

/-- Head virtual-share conversion with the collapsed-price dilution clamp. -/
def convertToShares (value totalValue totalSupply : Nat) : Nat :=
  let effectiveSupply := totalSupply + VIRTUAL_SHARES
  let denominator := totalValue + VIRTUAL_VALUE
  let clampedShares :=
    if mulDivUp effectiveSupply (WAD - MAX_MINT_DILUTION_WAD)
        MAX_MINT_DILUTION_WAD > denominator then
      mulDivDown effectiveSupply MAX_MINT_DILUTION_WAD
        (WAD - MAX_MINT_DILUTION_WAD)
    else UINT256_MAX
  min clampedShares (mulDivDown effectiveSupply value denominator)

structure FeeMintInput where
  stEffectiveNAV : Nat
  stTotalSupply : Nat
  jtEffectiveNAV : Nat
  jtTotalSupply : Nat
  lptLiquidityPremiumGross : Nat
  stProtocolFee : Nat
  jtProtocolFee : Nat
  lptProtocolFee : Nat
  deriving Repr, DecidableEq

structure FeeMintResult where
  retainedSTNAV : Nat
  retainedJTNAV : Nat
  lptLiquidityPremiumNet : Nat
  pooledProtocolFeeNAV : Nat
  lptOwnedSeniorTrancheSharesMinted : Nat
  protocolSeniorTrancheSharesMinted : Nat
  protocolJuniorTrancheSharesMinted : Nat
  stTotalSupplyAfterMints : Nat
  jtTotalSupplyAfterMint : Nat
  deriving Repr, DecidableEq

def processFeesAndLiquidityPremium (input : FeeMintInput) : FeeMintResult :=
  let retained :=
    input.stEffectiveNAV - input.lptLiquidityPremiumGross - input.stProtocolFee
  let retainedJT := input.jtEffectiveNAV - input.jtProtocolFee
  let lptNet := input.lptLiquidityPremiumGross - input.lptProtocolFee
  let pooledProtocolFee := input.stProtocolFee + input.lptProtocolFee
  let premiumShares := convertToShares lptNet retained input.stTotalSupply
  let protocolShares := convertToShares pooledProtocolFee retained input.stTotalSupply
  let jtProtocolShares :=
    convertToShares input.jtProtocolFee retainedJT input.jtTotalSupply
  {
    retainedSTNAV := retained
    retainedJTNAV := retainedJT
    lptLiquidityPremiumNet := lptNet
    pooledProtocolFeeNAV := pooledProtocolFee
    lptOwnedSeniorTrancheSharesMinted := premiumShares
    protocolSeniorTrancheSharesMinted := protocolShares
    protocolJuniorTrancheSharesMinted := jtProtocolShares
    stTotalSupplyAfterMints := input.stTotalSupply + premiumShares + protocolShares
    jtTotalSupplyAfterMint := input.jtTotalSupply + jtProtocolShares
  }

inductive Operation where
  | stDeposit
  | stRedemption
  | jtDeposit
  | jtRedemption
  | lptDeposit
  | lptRedemption
  deriving Repr, DecidableEq

structure PostOpInput where
  collateralNAV : Nat
  lptRawNAV : Nat
  stSelfLiquidationBonusNAV : Nat
  deriving Repr, DecidableEq

structure PostOpResult where
  accounting : AccountingState
  yields : YieldOutputs
  coverageUtilization : Nat
  liquidityUtilization : Nat
  deriving Repr, DecidableEq

/-- The accountant transition after one of the six accepted head-source shapes. -/
def postOpSyncTrancheAccounting
    (before : AccountingState)
    (op : Operation)
    (input : PostOpInput)
    (minCoverageWAD minLiquidityWAD : Nat) : PostOpResult :=
  let accounting : AccountingState := match op with
    | .stDeposit => {
        before with
        collateralNAV := input.collateralNAV
        lptRawNAV := input.lptRawNAV
        stEffectiveNAV := before.stEffectiveNAV +
          (input.collateralNAV - before.collateralNAV)
      }
    | .stRedemption =>
        let withdrawn := before.collateralNAV - input.collateralNAV
        {
          before with
          collateralNAV := input.collateralNAV
          lptRawNAV := input.lptRawNAV
          stEffectiveNAV := before.stEffectiveNAV -
            (withdrawn - input.stSelfLiquidationBonusNAV)
          jtEffectiveNAV := before.jtEffectiveNAV -
            input.stSelfLiquidationBonusNAV
        }
    | .jtDeposit => {
        before with
        collateralNAV := input.collateralNAV
        lptRawNAV := input.lptRawNAV
        jtEffectiveNAV := before.jtEffectiveNAV +
          (input.collateralNAV - before.collateralNAV)
      }
    | .jtRedemption => {
        before with
        collateralNAV := input.collateralNAV
        lptRawNAV := input.lptRawNAV
        jtEffectiveNAV := before.jtEffectiveNAV -
          (before.collateralNAV - input.collateralNAV)
      }
    | .lptDeposit | .lptRedemption => {
        before with
        collateralNAV := input.collateralNAV
        lptRawNAV := input.lptRawNAV
      }
  {
    accounting := accounting
    yields := YieldOutputs.zero
    coverageUtilization := coverageUtilizationWAD
      accounting.collateralNAV minCoverageWAD accounting.jtEffectiveNAV
    liquidityUtilization := liquidityUtilizationWAD
      accounting.stEffectiveNAV minLiquidityWAD accounting.lptRawNAV
  }

structure ReinvestmentState where
  accounting : AccountingState
  lptOwnedSeniorTrancheShares : Nat
  totalLPTAssets : Nat
  deriving Repr, DecidableEq

/-- Exact inner-leg storage update after oracle/slippage valuation. -/
def attemptLiquidityPremiumReinvestment
    (before : ReinvestmentState)
    (requestedShares minLPTAssetsOut lptAssetsMinted : Nat)
    (venueCallSucceeded : Bool) : ReinvestmentState :=
  let sharesToReinvest := min requestedShares before.lptOwnedSeniorTrancheShares
  if sharesToReinvest = 0 then
    before
  else if minLPTAssetsOut = 0 then
    before
  else if venueCallSucceeded && decide (minLPTAssetsOut ≤ lptAssetsMinted) then
    {
      before with
      lptOwnedSeniorTrancheShares :=
        before.lptOwnedSeniorTrancheShares - sharesToReinvest
      totalLPTAssets := before.totalLPTAssets + lptAssetsMinted
    }
  else
    before

end Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority
