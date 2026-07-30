import Benchmark.Cases.Starkware.StarkgateEscrow.Specs

namespace Benchmark.Cases.Starkware.StarkgateEscrow

theorem deposit_preserves_escrow_lower_bound
    (amount : Verity.Core.Uint256.Uint256) (s : ContractState)
    (hPre : escrow_lower_bound_spec s)
    (hAmountGt0 : amount.val > 0)
    (hAssetNoOverflow : (s.storage 0).val + amount.val < Verity.Core.Uint256.modulus)
    (hDepNoOverflow : (s.storage 1).val + amount.val < Verity.Core.Uint256.modulus) :
    let s' := ((StarkgateBridge.deposit amount).run s).snd
    deposit_preserves_escrow_lower_bound_spec s s' := by
  exact ?_

end Benchmark.Cases.Starkware.StarkgateEscrow
