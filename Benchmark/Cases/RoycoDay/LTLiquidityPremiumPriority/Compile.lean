import Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority.Specs

namespace Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority

#eval previewSyncTrancheAccounting
  dustCounterexampleLast
  dustCounterexampleCurrentRaw
  (.gain 20_000_000_000_000_000_000)
  (.gain 2)
  dustCounterexampleSyncConfig
  dustCounterexampleYieldConfig

#eval processFeesAndLiquidityPremium {
  stEffectiveNAV := 1_100_000_000_000_000_000_000
  stTotalSupply := 1_000_000_000_000_000_000_000
  ltLiquidityPremiumGross := 5_000_000_000_000_000_000
  stProtocolFee := 8_500_000_000_000_000_000
  ltYieldShareProtocolFee := 500_000_000_000_000_000
}

/--
Regression: preserve the source's single floor over a non-divisible time-weighted
premium window. Moving the floor before multiplying would produce `WAD - 2`.
-/
example : grossPremium (2 * WAD) (WAD - 1) 2 = WAD - 1 := by
  native_decide

/-- Regression: every supported post-op branch conserves a persisted valid state. -/
example
    (before : AccountingState)
    (op : Operation)
    (amounts : OperationAmounts)
    (minCoverageWAD minLiquidityWAD : Nat)
    (hDomain : successfulPostOpSourceDomain
      before op amounts minCoverageWAD minLiquidityWAD) :
    PostOpConservationSpec
      before op amounts minCoverageWAD minLiquidityWAD := by
  rcases hDomain with ⟨hConserves, _, _, _, _, hInput, _⟩
  unfold AccountingState.conserves at hConserves
  cases op <;>
    simp only [PostOpConservationSpec, postOpSyncTrancheAccountingUnchecked,
      AccountingState.conserves] <;>
    simp only [successfulPostOpInput] at hInput <;>
    omega

def nonConservingPostOpRegressionState : AccountingState := {
  raw := { stRawNAV := 1, jtRawNAV := 0, ltRawNAV := 0 }
  stEffectiveNAV := 0
  jtEffectiveNAV := 0
  jtCoverageImpermanentLoss := 0
}

def oneSTDepositRegressionAmounts : OperationAmounts := {
  stAmount := 1
  jtAmount := 0
  ltRawNAVAfter := 0
  stSelfLiquidationBonusNAV := 0
}

/-- Regression: the successful source domain rejects an invalid persisted state. -/
example : ¬ successfulPostOpSourceDomain
    nonConservingPostOpRegressionState
    .stDeposit
    oneSTDepositRegressionAmounts
    0
    0 := by
  intro hDomain
  have hConserves := hDomain.1
  norm_num [AccountingState.conserves, nonConservingPostOpRegressionState] at hConserves

end Benchmark.Cases.RoycoDay.LTLiquidityPremiumPriority
