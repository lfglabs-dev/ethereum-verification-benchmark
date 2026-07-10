import Benchmark.Cases.Starkware.StarkgateEscrow.Specs

namespace Benchmark.Cases.Starkware.StarkgateEscrow

theorem withdraw_preserves_escrow_lower_bound
    (amount : Verity.Core.Uint256.Uint256) (s : ContractState)
    (hPre : escrow_lower_bound_spec s)
    (hAmountLeBalance : amount.val <= (s.storage 0).val)
    (hWithdNoOverflow : (s.storage 2).val + amount.val < Verity.Core.Uint256.modulus) :
    let s' := ((StarkgateBridge.withdraw amount).run s).snd
    withdraw_preserves_escrow_lower_bound_spec s s' := by
  exact ?_

end Benchmark.Cases.Starkware.StarkgateEscrow
