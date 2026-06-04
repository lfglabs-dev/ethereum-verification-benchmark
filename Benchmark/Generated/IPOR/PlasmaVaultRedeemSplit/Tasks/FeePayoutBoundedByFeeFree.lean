import Benchmark.Cases.IPOR.PlasmaVaultRedeemSplit.Specs

namespace Benchmark.Cases.IPOR.PlasmaVaultRedeemSplit

theorem fee_payout_bounded_by_fee_free_task
    (amountShares feeRate : Nat) (s : VaultState) (m : Nat := virtualShares) :
    fee_payout_bounded_by_fee_free_spec amountShares feeRate s m := by
  exact ?_

end Benchmark.Cases.IPOR.PlasmaVaultRedeemSplit
