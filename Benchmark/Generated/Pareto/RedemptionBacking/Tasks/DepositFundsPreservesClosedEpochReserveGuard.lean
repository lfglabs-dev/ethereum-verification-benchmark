import Benchmark.Cases.Pareto.RedemptionBacking.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Pareto.RedemptionBacking

open Verity
open Verity.EVM.Uint256

theorem depositFunds_preserves_closed_epoch_reserve_guard
    (depositedScaled : Uint256) (s : ContractState)
    (hCollateralized : s.storage 5 != 0)
    (hDepositLeIdle : depositedScaled.val <= (s.storage 0).val)
    (hCurrentLeReserved : (s.storage 3).val <= (s.storage 2).val)
    (hAddNoOverflow :
      (sub (s.storage 0) depositedScaled).val + (s.storage 1).val <
        Verity.Core.Uint256.modulus)
    (hReserveGuard :
      (sub (s.storage 2) (s.storage 3)).val <=
        (add (sub (s.storage 0) depositedScaled) (s.storage 1)).val) :
    let s' := ((ParetoDollarQueue.depositFunds depositedScaled).run s).snd
    depositFunds_preserves_closed_epoch_reserve_guard_spec s s' := by
  exact ?_

end Benchmark.Cases.Pareto.RedemptionBacking
