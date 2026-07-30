import Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority.Specs

namespace Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority

#eval previewSyncTrancheAccounting partialRecoveryLast
  (partialRecoveryLast.collateralNAV + 2) partialRecoverySyncConfig
  partialRecoveryYieldConfig

#eval processFeesAndLiquidityPremium {
  stEffectiveNAV := 1_100_000_000_000_000_000_000
  stTotalSupply := 1_000_000_000_000_000_000_000
  jtEffectiveNAV := 200_000_000_000_000_000_000
  jtTotalSupply := 180_000_000_000_000_000_000
  lptLiquidityPremiumGross := 5_000_000_000_000_000_000
  stProtocolFee := 8_500_000_000_000_000_000
  jtProtocolFee := 250_000_000_000_000_000
  lptProtocolFee := 500_000_000_000_000_000
}

def clampOverflowMintInput : FeeMintInput := {
  stEffectiveNAV := 0
  stTotalSupply := UINT256_MAX - 1
  jtEffectiveNAV := 0
  jtTotalSupply := 0
  lptLiquidityPremiumGross := 0
  stProtocolFee := 0
  jtProtocolFee := 0
  lptProtocolFee := 0
}

/-- Solidity's eager dilution-clamp mulDiv overflows on this Nat-model witness. -/
example : ¬ successfulMintDomain clampOverflowMintInput := by
  unfold successfulMintDomain convertToSharesSourceSafe
  norm_num [clampOverflowMintInput, processFeesAndLiquidityPremium,
    FeeMintInput.uint256Bounded, FeeMintResult.uint256Bounded,
    convertToShares, mulDivDown, mulDivUp, VIRTUAL_SHARES, VIRTUAL_VALUE,
    MAX_MINT_DILUTION_WAD, WAD, UINT256_MAX]

/-- Preserve the source's single floor over a non-divisible accumulator window. -/
example : grossPremium (2 * WAD) (WAD - 1) 2 = WAD - 1 := by
  native_decide

/-- The head regression has no residual gain and therefore cannot mint fees. -/
example :
    let result := previewSyncTrancheAccounting partialRecoveryLast
      (partialRecoveryLast.collateralNAV + 2) partialRecoverySyncConfig
      partialRecoveryYieldConfig
    result.remainingImpermanentLossBeforeTransition = 3 ∧
      result.outputs = YieldOutputs.zero := by
  native_decide

def nonConservingPostOpRegressionState : AccountingState := {
  marketState := .fixedTerm
  collateralNAV := 1
  lptRawNAV := 0
  stEffectiveNAV := 0
  jtEffectiveNAV := 0
  jtImpermanentLoss := 0
}

def oneSTDepositRegressionInput : PostOpInput := {
  collateralNAV := 2
  lptRawNAV := 0
  stSelfLiquidationBonusNAV := 0
}

/-- The successful source domain rejects an invalid persisted accounting state. -/
example : ¬ successfulPostOpSourceDomain
    nonConservingPostOpRegressionState
    .stDeposit
    oneSTDepositRegressionInput
    0
    0 := by
  intro hDomain
  have hConserves := hDomain.1
  norm_num [AccountingState.conserves, nonConservingPostOpRegressionState] at hConserves

end Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority
