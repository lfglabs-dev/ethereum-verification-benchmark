import Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority.Contract

namespace Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority

def signedDeltasMatchRaw
    (last : AccountingState)
    (current : RawNAVs)
    (deltaJT deltaST : SignedDelta) : Prop :=
  let oldTotal := last.raw.stRawNAV + last.raw.jtRawNAV
  let newTotal := current.stRawNAV + current.jtRawNAV
  match deltaJT, deltaST with
  | .gain jt, .gain st => newTotal = oldTotal + jt + st
  | .gain jt, .flat => newTotal = oldTotal + jt
  | .gain jt, .loss st => newTotal + st = oldTotal + jt
  | .flat, .gain st => newTotal = oldTotal + st
  | .flat, .flat => newTotal = oldTotal
  | .flat, .loss st => newTotal + st = oldTotal
  | .loss jt, .gain st => newTotal + jt = oldTotal + st
  | .loss jt, .flat => newTotal + jt = oldTotal
  | .loss jt, .loss st => newTotal + jt + st = oldTotal

def successfulSyncDomain
    (last : AccountingState)
    (current : RawNAVs)
    (deltaJT deltaST : SignedDelta)
    (syncCfg : SyncConfig)
    (yieldCfg : YieldConfig) : Prop :=
  let jtStep := applyJTEffectiveDelta
    last.jtEffectiveNAV deltaJT
    syncCfg.effectiveNAVDustTolerance yieldCfg.jtProtocolFeeWAD
  last.conserves ∧
    yieldCfg.valid ∧
    signedDeltasMatchRaw last current deltaJT deltaST ∧
    (match deltaJT with
      | .loss loss => loss ≤ last.jtEffectiveNAV
      | _ => True) ∧
    (match deltaST with
      | .loss loss =>
          loss - min loss jtStep.jtEffectiveNAV ≤ last.stEffectiveNAV
      | _ => True)

/-!
## Nat-to-uint256 refinement boundary

The implementation model uses unbounded naturals for tractable proofs. These
predicates describe the successful Solidity boundary: source inputs, checked
arithmetic results, full-precision `mulDiv` quotients, and committed outputs
must fit `uint256`. Every source-facing theorem receives the matching premise.
-/

def RawNAVs.uint256Bounded (raw : RawNAVs) : Prop :=
  raw.stRawNAV ≤ UINT256_MAX ∧
    raw.jtRawNAV ≤ UINT256_MAX ∧
    raw.ltRawNAV ≤ UINT256_MAX ∧
    raw.stRawNAV + raw.jtRawNAV ≤ UINT256_MAX

def AccountingState.uint256Bounded (s : AccountingState) : Prop :=
  s.raw.uint256Bounded ∧
    s.stEffectiveNAV ≤ UINT256_MAX ∧
    s.jtEffectiveNAV ≤ UINT256_MAX ∧
    s.jtCoverageImpermanentLoss ≤ UINT256_MAX ∧
    s.stEffectiveNAV + s.jtEffectiveNAV ≤ UINT256_MAX

def YieldConfig.uint256Bounded (cfg : YieldConfig) : Prop :=
  cfg.elapsedSinceLastPremiumPayments ≤ UINT256_MAX ∧
    cfg.twJTYieldShareAccruedWAD ≤ UINT256_MAX ∧
    cfg.twLTYieldShareAccruedWAD ≤ UINT256_MAX ∧
    cfg.elapsedSinceLastPremiumPayments * WAD ≤ UINT256_MAX ∧
    cfg.stProtocolFeeWAD ≤ UINT256_MAX ∧
    cfg.jtProtocolFeeWAD ≤ UINT256_MAX ∧
    cfg.jtYieldShareProtocolFeeWAD ≤ UINT256_MAX ∧
    cfg.ltYieldShareProtocolFeeWAD ≤ UINT256_MAX

def SyncConfig.uint256Bounded (cfg : SyncConfig) : Prop :=
  cfg.effectiveNAVDustTolerance ≤ UINT256_MAX ∧
    cfg.minCoverageWAD ≤ UINT256_MAX ∧
    cfg.minLiquidityWAD ≤ UINT256_MAX

def SyncResult.uint256Bounded (result : SyncResult) : Prop :=
  result.accounting.uint256Bounded ∧
    result.outputs.ltLiquidityPremium ≤ UINT256_MAX ∧
    result.outputs.stProtocolFee ≤ UINT256_MAX ∧
    result.outputs.jtProtocolFee ≤ UINT256_MAX ∧
    result.outputs.ltProtocolFee ≤ UINT256_MAX ∧
    result.recoveredCoverageIL ≤ UINT256_MAX ∧
    result.remainingCoverageILBeforeTransition ≤ UINT256_MAX ∧
    result.residualSeniorYield ≤ UINT256_MAX ∧
    result.jtRiskPremiumGross ≤ UINT256_MAX ∧
    result.jtYieldShareProtocolFee ≤ UINT256_MAX ∧
    result.priorJTPnlProtocolFee ≤ UINT256_MAX ∧
    result.jtCoverageApplied ≤ UINT256_MAX ∧
    result.residualSeniorLoss ≤ UINT256_MAX ∧
    result.coverageUtilization ≤ UINT256_MAX ∧
    result.liquidityUtilization ≤ UINT256_MAX

/-- Checked intermediate additions/subtractions on the source-ordered sync path. -/
def syncIntermediateUint256Safe
    (last : AccountingState)
    (deltaJT deltaST : SignedDelta)
    (syncCfg : SyncConfig)
    (yieldCfg : YieldConfig) : Prop :=
  let jtStep := applyJTEffectiveDelta
    last.jtEffectiveNAV deltaJT
    syncCfg.effectiveNAVDustTolerance yieldCfg.jtProtocolFeeWAD
  (match deltaJT with
    | .loss loss => loss ≤ last.jtEffectiveNAV
    | .flat => True
    | .gain gain => last.jtEffectiveNAV + gain ≤ UINT256_MAX) ∧
  (match deltaST with
    | .flat => True
    | .loss loss =>
        let coverage := min loss jtStep.jtEffectiveNAV
        let residual := loss - coverage
        residual ≤ last.stEffectiveNAV ∧
          last.jtCoverageImpermanentLoss + coverage ≤ UINT256_MAX
    | .gain gain =>
        let recovered := min gain last.jtCoverageImpermanentLoss
        let residual := gain - recovered
        let jtPremium := grossPremium residual yieldCfg.twJTYieldShareAccruedWAD
          yieldCfg.elapsedSinceLastPremiumPayments
        let ltPremium := grossPremium residual yieldCfg.twLTYieldShareAccruedWAD
          yieldCfg.elapsedSinceLastPremiumPayments
        let jtYieldFee :=
          if residual > syncCfg.effectiveNAVDustTolerance then
            mulDivDown jtPremium yieldCfg.jtYieldShareProtocolFeeWAD WAD
          else 0
        last.stEffectiveNAV + residual ≤ UINT256_MAX ∧
          jtPremium + ltPremium ≤ residual ∧
          jtStep.jtEffectiveNAV + recovered ≤ UINT256_MAX ∧
          jtStep.jtEffectiveNAV + recovered + jtPremium ≤ UINT256_MAX ∧
          jtStep.jtProtocolFee + jtYieldFee ≤ UINT256_MAX)

/--
The modeled waterfall begins after Royco Day computes raw NAV deltas and attributes
them to effective ST/JT PnL. This predicate records the successful source prelude:
both raw operands accepted the source's checked `toInt256`, and the supplied signed
attribution outputs are representable results of that omitted signed-arithmetic step.
-/
def sourceAttributionInt256Safe
    (last : AccountingState)
    (current : RawNAVs)
    (deltaJT deltaST : SignedDelta) : Prop :=
  last.raw.stRawNAV ≤ INT256_MAX ∧
    last.raw.jtRawNAV ≤ INT256_MAX ∧
    current.stRawNAV ≤ INT256_MAX ∧
    current.jtRawNAV ≤ INT256_MAX ∧
    (match deltaJT with
      | .loss amount | .gain amount => amount ≤ INT256_MAX
      | .flat => True) ∧
    (match deltaST with
      | .loss amount | .gain amount => amount ≤ INT256_MAX
      | .flat => True) ∧
    deltaJT.magnitude + deltaST.magnitude ≤ INT256_MAX

def sourceSyncDomain
    (last : AccountingState)
    (current : RawNAVs)
    (deltaJT deltaST : SignedDelta)
    (syncCfg : SyncConfig)
    (yieldCfg : YieldConfig) : Prop :=
  successfulSyncDomain last current deltaJT deltaST syncCfg yieldCfg ∧
    syncIntermediateUint256Safe last deltaJT deltaST syncCfg yieldCfg ∧
    sourceAttributionInt256Safe last current deltaJT deltaST ∧
    last.uint256Bounded ∧
    current.uint256Bounded ∧
    syncCfg.uint256Bounded ∧
    yieldCfg.uint256Bounded ∧
    (match deltaJT with
      | .loss amount | .gain amount => amount ≤ UINT256_MAX
      | .flat => True) ∧
    (match deltaST with
      | .loss amount | .gain amount => amount ≤ UINT256_MAX
      | .flat => True) ∧
    (previewSyncTrancheAccounting
      last current deltaJT deltaST syncCfg yieldCfg).uint256Bounded

/-- A natural is represented exactly, rather than reduced modulo `2^256`. -/
def natUint256EncodingExact (n : Nat) : Prop :=
  (Verity.Core.Uint256.ofNat n).val = n

/-- A signed source operand/result round-trips exactly through Verity `Int256`. -/
def int256EncodingExact (value : Int) : Prop :=
  ((Verity.Core.Int256.ofInt value : Verity.Core.Int256) : Int) = value

def natInt256EncodingExact (n : Nat) : Prop :=
  int256EncodingExact (Int.ofNat n)

def RawNAVs.sourceInt256EncodingExact (raw : RawNAVs) : Prop :=
  natInt256EncodingExact raw.stRawNAV ∧
    natInt256EncodingExact raw.jtRawNAV

def RawNAVs.uint256EncodingExact (raw : RawNAVs) : Prop :=
  natUint256EncodingExact raw.stRawNAV ∧
    natUint256EncodingExact raw.jtRawNAV ∧
    natUint256EncodingExact raw.ltRawNAV

def AccountingState.uint256EncodingExact (s : AccountingState) : Prop :=
  s.raw.uint256EncodingExact ∧
    natUint256EncodingExact s.stEffectiveNAV ∧
    natUint256EncodingExact s.jtEffectiveNAV ∧
    natUint256EncodingExact s.jtCoverageImpermanentLoss

def YieldConfig.uint256EncodingExact (cfg : YieldConfig) : Prop :=
  natUint256EncodingExact cfg.elapsedSinceLastPremiumPayments ∧
    natUint256EncodingExact cfg.twJTYieldShareAccruedWAD ∧
    natUint256EncodingExact cfg.twLTYieldShareAccruedWAD ∧
    natUint256EncodingExact cfg.stProtocolFeeWAD ∧
    natUint256EncodingExact cfg.jtProtocolFeeWAD ∧
    natUint256EncodingExact cfg.jtYieldShareProtocolFeeWAD ∧
    natUint256EncodingExact cfg.ltYieldShareProtocolFeeWAD

def SyncConfig.uint256EncodingExact (cfg : SyncConfig) : Prop :=
  natUint256EncodingExact cfg.effectiveNAVDustTolerance ∧
    natUint256EncodingExact cfg.minCoverageWAD ∧
    natUint256EncodingExact cfg.minLiquidityWAD

def SignedDelta.uint256EncodingExact (delta : SignedDelta) : Prop :=
  match delta with
  | .loss amount | .gain amount => natUint256EncodingExact amount
  | .flat => True

def SignedDelta.int256EncodingExact (delta : SignedDelta) : Prop :=
  match delta with
  | .loss amount =>
      Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority.int256EncodingExact
        (-(Int.ofNat amount))
  | .flat =>
      Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority.int256EncodingExact 0
  | .gain amount =>
      Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority.int256EncodingExact
        (Int.ofNat amount)

def YieldOutputs.uint256EncodingExact (outputs : YieldOutputs) : Prop :=
  natUint256EncodingExact outputs.ltLiquidityPremium ∧
    natUint256EncodingExact outputs.stProtocolFee ∧
    natUint256EncodingExact outputs.jtProtocolFee ∧
    natUint256EncodingExact outputs.ltProtocolFee

def SyncResult.uint256EncodingExact (result : SyncResult) : Prop :=
  result.accounting.uint256EncodingExact ∧
    result.outputs.uint256EncodingExact ∧
    natUint256EncodingExact result.recoveredCoverageIL ∧
    natUint256EncodingExact result.remainingCoverageILBeforeTransition ∧
    natUint256EncodingExact result.residualSeniorYield ∧
    natUint256EncodingExact result.jtRiskPremiumGross ∧
    natUint256EncodingExact result.jtYieldShareProtocolFee ∧
    natUint256EncodingExact result.priorJTPnlProtocolFee ∧
    natUint256EncodingExact result.jtCoverageApplied ∧
    natUint256EncodingExact result.residualSeniorLoss ∧
    natUint256EncodingExact result.coverageUtilization ∧
    natUint256EncodingExact result.liquidityUtilization

/-- Solidity-0.8 checked addition and subtraction agree with natural arithmetic. -/
def checkedArithmeticRefinesNat : Prop :=
  ∀ a b : Nat,
    a ≤ UINT256_MAX →
    b ≤ UINT256_MAX →
    (a + b ≤ UINT256_MAX →
      Verity.Stdlib.Math.safeAdd
        (Verity.Core.Uint256.ofNat a)
        (Verity.Core.Uint256.ofNat b) =
          some (Verity.Core.Uint256.ofNat (a + b))) ∧
    (b ≤ a →
      Verity.Stdlib.Math.safeSub
        (Verity.Core.Uint256.ofNat a)
        (Verity.Core.Uint256.ofNat b) =
          some (Verity.Core.Uint256.ofNat (a - b)))

/-- Verity's full-precision floor/ceil helpers agree with the natural model. -/
def fullPrecisionMulDivRefinesNat : Prop :=
  ∀ a b denominator : Nat,
    a ≤ UINT256_MAX →
    b ≤ UINT256_MAX →
    denominator ≤ UINT256_MAX →
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

/--
Semantic refinement proposition for a successful source sync. It constructs exact
`Uint256` encodings for the actual inputs/result, exact sign-preserving `Int256`
encodings for source PnL attribution operands/results, and proves checked add/sub plus
full-precision floor/ceil multiply-divide agree with the natural-number model.
-/
def NatUint256RefinementSpec
    (last : AccountingState)
    (current : RawNAVs)
    (deltaJT deltaST : SignedDelta)
    (syncCfg : SyncConfig)
    (yieldCfg : YieldConfig) : Prop :=
  let result := previewSyncTrancheAccounting
    last current deltaJT deltaST syncCfg yieldCfg
  last.uint256EncodingExact ∧
    current.uint256EncodingExact ∧
    last.raw.sourceInt256EncodingExact ∧
    current.sourceInt256EncodingExact ∧
    deltaJT.uint256EncodingExact ∧
    deltaST.uint256EncodingExact ∧
    deltaJT.int256EncodingExact ∧
    deltaST.int256EncodingExact ∧
    syncCfg.uint256EncodingExact ∧
    yieldCfg.uint256EncodingExact ∧
    result.uint256EncodingExact ∧
    checkedArithmeticRefinesNat ∧
    fullPrecisionMulDivRefinesNat

/-- Recovery consumes `min(gain, IL)` before any ST-sourced yield share. -/
def RecoveryBeforeYieldSpec
    (last : AccountingState)
    (current : RawNAVs)
    (deltaJT : SignedDelta)
    (stGain : Nat)
    (syncCfg : SyncConfig)
    (yieldCfg : YieldConfig) : Prop :=
  let result := previewSyncTrancheAccounting
    last current deltaJT (.gain stGain) syncCfg yieldCfg
  result.recoveredCoverageIL = min stGain last.jtCoverageImpermanentLoss ∧
    result.remainingCoverageILBeforeTransition =
      last.jtCoverageImpermanentLoss - result.recoveredCoverageIL ∧
    result.residualSeniorYield = stGain - result.recoveredCoverageIL ∧
    (stGain ≤ last.jtCoverageImpermanentLoss →
      result.residualSeniorYield = 0 ∧
      result.jtRiskPremiumGross = 0 ∧
      result.outputs.ltLiquidityPremium = 0 ∧
      result.outputs.stProtocolFee = 0 ∧
      result.jtYieldShareProtocolFee = 0 ∧
      result.outputs.ltProtocolFee = 0)

/-- The two gross yield shares cannot exceed residual senior yield. -/
def CombinedPremiumBoundSpec
    (stGain coverageIL : Nat)
    (cfg : YieldConfig) : Prop :=
  let residual := residualSeniorYield stGain coverageIL
  grossPremium residual cfg.twJTYieldShareAccruedWAD
      cfg.elapsedSinceLastPremiumPayments +
    grossPremium residual cfg.twLTYieldShareAccruedWAD
      cfg.elapsedSinceLastPremiumPayments ≤ residual

/-- Changing only LT's accrued numerator cannot change ST/JT accounting or utilization. -/
def LTPremiumCoverageNeutralSpec
    (last : AccountingState)
    (current : RawNAVs)
    (deltaJT deltaST : SignedDelta)
    (syncCfg : SyncConfig)
    (cfg : YieldConfig)
    (ltAccruedA ltAccruedB : Nat) : Prop :=
  let cfgA := { cfg with twLTYieldShareAccruedWAD := ltAccruedA }
  let cfgB := { cfg with twLTYieldShareAccruedWAD := ltAccruedB }
  let resultA := previewSyncTrancheAccounting
    last current deltaJT deltaST syncCfg cfgA
  let resultB := previewSyncTrancheAccounting
    last current deltaJT deltaST syncCfg cfgB
  resultA.accounting = resultB.accounting ∧
    resultA.coverageUtilization = resultB.coverageUtilization ∧
    resultA.liquidityUtilization = resultB.liquidityUtilization

/-- Gross LT NAV splits exactly, then each recipient uses exact source conversion. -/
def LTPremiumMintSplitSpec (input : FeeMintInput) : Prop :=
  let result := processFeesAndLiquidityPremium input
  result.ltLiquidityPremiumNet + input.ltYieldShareProtocolFee =
      input.ltLiquidityPremiumGross ∧
    result.pooledProtocolFeeNAV =
      input.stProtocolFee + input.ltYieldShareProtocolFee ∧
    result.ltOwnedSeniorTrancheSharesMinted =
      convertToShares
        result.ltLiquidityPremiumNet result.retainedSTNAV input.stTotalSupply ∧
    result.protocolSeniorTrancheSharesMinted =
      convertToShares
        result.pooledProtocolFeeNAV result.retainedSTNAV input.stTotalSupply ∧
    result.stTotalSupplyAfterMints =
      input.stTotalSupply +
        result.ltOwnedSeniorTrancheSharesMinted +
        result.protocolSeniorTrancheSharesMinted

def FeeMintInput.uint256Bounded (input : FeeMintInput) : Prop :=
  input.stEffectiveNAV ≤ UINT256_MAX ∧
    input.stTotalSupply ≤ UINT256_MAX ∧
    input.ltLiquidityPremiumGross ≤ UINT256_MAX ∧
    input.stProtocolFee ≤ UINT256_MAX ∧
    input.ltYieldShareProtocolFee ≤ UINT256_MAX

def FeeMintResult.uint256Bounded (result : FeeMintResult) : Prop :=
  result.retainedSTNAV ≤ UINT256_MAX ∧
    result.ltLiquidityPremiumNet ≤ UINT256_MAX ∧
    result.pooledProtocolFeeNAV ≤ UINT256_MAX ∧
    result.ltOwnedSeniorTrancheSharesMinted ≤ UINT256_MAX ∧
    result.protocolSeniorTrancheSharesMinted ≤ UINT256_MAX ∧
    result.stTotalSupplyAfterMints ≤ UINT256_MAX

def successfulMintDomain (input : FeeMintInput) : Prop :=
  input.uint256Bounded ∧
    input.ltYieldShareProtocolFee ≤ input.ltLiquidityPremiumGross ∧
    input.ltLiquidityPremiumGross + input.stProtocolFee ≤ input.stEffectiveNAV ∧
    (processFeesAndLiquidityPremium input).uint256Bounded

/-- ST loss is absorbed by JT first and creates an equal IL liability. -/
def STLossCoveragePrioritySpec
    (last : AccountingState)
    (current : RawNAVs)
    (deltaJT : SignedDelta)
    (stLoss : Nat)
    (syncCfg : SyncConfig)
    (yieldCfg : YieldConfig) : Prop :=
  let jtStep := applyJTEffectiveDelta
    last.jtEffectiveNAV deltaJT
    syncCfg.effectiveNAVDustTolerance yieldCfg.jtProtocolFeeWAD
  let result := previewSyncTrancheAccounting
    last current deltaJT (.loss stLoss) syncCfg yieldCfg
  result.jtCoverageApplied = min stLoss jtStep.jtEffectiveNAV ∧
    result.residualSeniorLoss = stLoss - result.jtCoverageApplied ∧
    result.remainingCoverageILBeforeTransition =
      last.jtCoverageImpermanentLoss + result.jtCoverageApplied ∧
    result.outputs.ltLiquidityPremium = 0 ∧
    result.outputs.stProtocolFee = 0 ∧
    result.outputs.ltProtocolFee = 0

/-- Full source-ordered sync conserves ST/JT NAV on its successful domain. -/
def SyncConservationSpec
    (last : AccountingState)
    (current : RawNAVs)
    (deltaJT deltaST : SignedDelta)
    (syncCfg : SyncConfig)
    (yieldCfg : YieldConfig) : Prop :=
  (previewSyncTrancheAccounting
    last current deltaJT deltaST syncCfg yieldCfg).accounting.conserves

def successfulPostOpInput
    (before : AccountingState)
    (op : Operation)
    (amounts : OperationAmounts) : Prop :=
  match op with
  | .stDeposit =>
      0 < amounts.stAmount ∧
      amounts.jtAmount = 0 ∧
      amounts.ltRawNAVAfter = before.raw.ltRawNAV ∧
      amounts.stSelfLiquidationBonusNAV = 0
  | .jtDeposit =>
      amounts.stAmount = 0 ∧
      0 < amounts.jtAmount ∧
      amounts.ltRawNAVAfter = before.raw.ltRawNAV ∧
      amounts.stSelfLiquidationBonusNAV = 0
  | .ltDeposit =>
      before.raw.ltRawNAV < amounts.ltRawNAVAfter ∧
      amounts.jtAmount = 0 ∧
      amounts.stSelfLiquidationBonusNAV = 0
  | .stRedeem =>
      amounts.ltRawNAVAfter = before.raw.ltRawNAV ∧
      0 < amounts.stAmount + amounts.jtAmount ∧
      amounts.stAmount ≤ before.raw.stRawNAV ∧
      amounts.jtAmount ≤ before.raw.jtRawNAV ∧
      amounts.stSelfLiquidationBonusNAV ≤ amounts.stAmount + amounts.jtAmount ∧
      amounts.stSelfLiquidationBonusNAV ≤ before.jtEffectiveNAV ∧
      amounts.stAmount + amounts.jtAmount - amounts.stSelfLiquidationBonusNAV ≤
        before.stEffectiveNAV
  | .jtRedeem =>
      amounts.ltRawNAVAfter = before.raw.ltRawNAV ∧
      0 < amounts.stAmount + amounts.jtAmount ∧
      amounts.stAmount ≤ before.raw.stRawNAV ∧
      amounts.jtAmount ≤ before.raw.jtRawNAV ∧
      amounts.stAmount + amounts.jtAmount ≤ before.jtEffectiveNAV ∧
      amounts.stSelfLiquidationBonusNAV = 0
  | .ltRedeem =>
      amounts.ltRawNAVAfter ≤ before.raw.ltRawNAV ∧
      amounts.stAmount ≤ before.raw.stRawNAV ∧
      amounts.jtAmount ≤ before.raw.jtRawNAV ∧
      amounts.stSelfLiquidationBonusNAV ≤ amounts.stAmount + amounts.jtAmount ∧
      amounts.stSelfLiquidationBonusNAV ≤ before.jtEffectiveNAV ∧
      amounts.stAmount + amounts.jtAmount - amounts.stSelfLiquidationBonusNAV ≤
        before.stEffectiveNAV

def OperationAmounts.uint256Bounded (amounts : OperationAmounts) : Prop :=
  amounts.stAmount ≤ UINT256_MAX ∧
    amounts.jtAmount ≤ UINT256_MAX ∧
    amounts.ltRawNAVAfter ≤ UINT256_MAX ∧
    amounts.stSelfLiquidationBonusNAV ≤ UINT256_MAX ∧
    amounts.stAmount + amounts.jtAmount ≤ UINT256_MAX

def PostOpResult.uint256Bounded (result : PostOpResult) : Prop :=
  result.accounting.uint256Bounded ∧
    result.coverageUtilization ≤ UINT256_MAX ∧
    result.liquidityUtilization ≤ UINT256_MAX

def successfulPostOpSourceDomain
    (before : AccountingState)
    (op : Operation)
    (amounts : OperationAmounts)
    (minCoverageWAD minLiquidityWAD : Nat) : Prop :=
  before.conserves ∧
    before.uint256Bounded ∧
    amounts.uint256Bounded ∧
    minCoverageWAD ≤ UINT256_MAX ∧
    minLiquidityWAD ≤ UINT256_MAX ∧
    successfulPostOpInput before op amounts ∧
    (postOpSyncTrancheAccountingUnchecked
      before op amounts minCoverageWAD minLiquidityWAD).uint256Bounded

def PostOpNoYieldSpec
    (before : AccountingState)
    (op : Operation)
    (amounts : OperationAmounts)
    (minCoverageWAD minLiquidityWAD : Nat) : Prop :=
  (postOpSyncTrancheAccountingUnchecked
    before op amounts minCoverageWAD minLiquidityWAD).yields = YieldOutputs.zero

def PostOpConservationSpec
    (before : AccountingState)
    (op : Operation)
    (amounts : OperationAmounts)
    (minCoverageWAD minLiquidityWAD : Nat) : Prop :=
  (postOpSyncTrancheAccountingUnchecked
    before op amounts minCoverageWAD minLiquidityWAD).accounting.conserves

/-- Exact success/failure reinvestment cannot mutate ST/JT coverage accounting. -/
def InnerReinvestmentCoverageNeutralSpec
    (before : ReinvestmentState)
    (requestedShares minLTAssetsOut ltAssetsMinted minCoverageWAD : Nat)
    (venueCallSucceeded : Bool) : Prop :=
  let after := attemptLiquidityPremiumReinvestment
    before requestedShares minLTAssetsOut ltAssetsMinted venueCallSucceeded
  after.accounting = before.accounting ∧
    coverageUtilizationWAD
      after.accounting.raw minCoverageWAD after.accounting.jtEffectiveNAV =
    coverageUtilizationWAD
      before.accounting.raw minCoverageWAD before.accounting.jtEffectiveNAV

def ReinvestmentState.uint256Bounded (state : ReinvestmentState) : Prop :=
  state.accounting.uint256Bounded ∧
    state.ltOwnedSeniorTrancheShares ≤ UINT256_MAX ∧
    state.ltOwnedYieldBearingAssets ≤ UINT256_MAX

def successfulReinvestmentDomain
    (before : ReinvestmentState)
    (requestedShares minLTAssetsOut ltAssetsMinted minCoverageWAD : Nat)
    (venueCallSucceeded : Bool) : Prop :=
  before.uint256Bounded ∧
    requestedShares ≤ UINT256_MAX ∧
    minLTAssetsOut ≤ UINT256_MAX ∧
    ltAssetsMinted ≤ UINT256_MAX ∧
    minCoverageWAD ≤ UINT256_MAX ∧
    (attemptLiquidityPremiumReinvestment
      before requestedShares minLTAssetsOut ltAssetsMinted
      venueCallSucceeded).uint256Bounded

/-- Concrete sign regressions: losses encode as negative words; gains stay positive. -/
example : (SignedDelta.loss 1).int256EncodingExact := by rfl

example : (SignedDelta.gain 1).int256EncodingExact := by rfl

def int256BoundaryRejectedLast : AccountingState := {
  raw := { stRawNAV := 2 ^ 255, jtRawNAV := 0, ltRawNAV := 0 }
  stEffectiveNAV := 2 ^ 255
  jtEffectiveNAV := 0
  jtCoverageImpermanentLoss := 0
}

def int256BoundaryRejectedCurrent : RawNAVs := {
  stRawNAV := 2 ^ 255
  jtRawNAV := 0
  ltRawNAV := 0
}

/-- The top-bit witness fits uint256 but the source's checked `toInt256` rejects it. -/
example : ¬ sourceAttributionInt256Safe
    int256BoundaryRejectedLast int256BoundaryRejectedCurrent .flat .flat := by
  norm_num [sourceAttributionInt256Safe, int256BoundaryRejectedLast,
    int256BoundaryRejectedCurrent, INT256_MAX]

def dustCounterexampleLast : AccountingState := {
  raw := {
    stRawNAV := 1_000_000_000_000_000_000_000
    jtRawNAV := 200_000_000_000_000_000_000
    ltRawNAV := 0
  }
  stEffectiveNAV := 1_000_000_000_000_000_000_005
  jtEffectiveNAV := 199_999_999_999_999_999_995
  jtCoverageImpermanentLoss := 5
}

def dustCounterexampleCurrentRaw : RawNAVs := {
  stRawNAV := 1_000_000_000_000_000_000_002
  jtRawNAV := 220_000_000_000_000_000_000
  ltRawNAV := 0
}

def dustCounterexampleYieldConfig : YieldConfig := {
  elapsedSinceLastPremiumPayments := 1
  twJTYieldShareAccruedWAD := 100_000_000_000_000_000
  twLTYieldShareAccruedWAD := 50_000_000_000_000_000
  stProtocolFeeWAD := 100_000_000_000_000_000
  jtProtocolFeeWAD := 100_000_000_000_000_000
  jtYieldShareProtocolFeeWAD := 100_000_000_000_000_000
  ltYieldShareProtocolFeeWAD := 100_000_000_000_000_000
}

def dustCounterexampleSyncConfig : SyncConfig := {
  effectiveNAVDustTolerance := 7
  minCoverageWAD := 100_000_000_000_000_000
  minLiquidityWAD := 0
  resultingMarketState := .perpetual
  eraseCoverageIL := false
}

/--
Concrete pinned-source counterexample to the broad no-fee wording: concurrent JT
appreciation creates a 2e18 JT fee while a 2-wei senior recovery leaves 3 wei IL.
-/
def IndependentJTFeeCounterexampleSpec : Prop :=
  let result := previewSyncTrancheAccounting
    dustCounterexampleLast
    dustCounterexampleCurrentRaw
    (.gain 20_000_000_000_000_000_000)
    (.gain 2)
    dustCounterexampleSyncConfig
    dustCounterexampleYieldConfig
  sourceSyncDomain
      dustCounterexampleLast
      dustCounterexampleCurrentRaw
      (.gain 20_000_000_000_000_000_000)
      (.gain 2)
      dustCounterexampleSyncConfig
      dustCounterexampleYieldConfig ∧
    result.accounting.conserves ∧
    result.recoveredCoverageIL = 2 ∧
    result.remainingCoverageILBeforeTransition = 3 ∧
    result.residualSeniorYield = 0 ∧
    result.jtRiskPremiumGross = 0 ∧
    result.outputs.ltLiquidityPremium = 0 ∧
    result.outputs.jtProtocolFee = 2_000_000_000_000_000_000

end Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority
