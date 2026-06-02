import Benchmark.Cases.IPOR.PlasmaVaultRedeemSplit.Specs

namespace Benchmark.Cases.IPOR.PlasmaVaultRedeemSplit

theorem old_split_bound_under_bounded_advantage_task
    (s1 s2 feeRate roundingSlack : Nat) (s : VaultState) (m : Nat := virtualShares) :
    old_split_bound_under_bounded_advantage_spec s1 s2 feeRate roundingSlack s m := by
  exact ?_

end Benchmark.Cases.IPOR.PlasmaVaultRedeemSplit
