import Benchmark.Cases.IPOR.PlasmaVaultRedeemSplit.Specs

namespace Benchmark.Cases.IPOR.PlasmaVaultRedeemSplit

theorem redeem_preserves_pps_task
    (amountShares feeRate : Nat) (s : VaultState) (m : Nat := virtualShares) :
    redeem_preserves_pps_spec amountShares feeRate s m := by
  exact ?_

end Benchmark.Cases.IPOR.PlasmaVaultRedeemSplit
