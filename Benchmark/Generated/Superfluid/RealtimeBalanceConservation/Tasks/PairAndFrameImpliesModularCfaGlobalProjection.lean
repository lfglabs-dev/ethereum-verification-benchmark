import Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Contract
import Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Specs

namespace Benchmark.Cases.Superfluid.RealtimeBalanceConservation

open Verity

theorem pairAndFrame_implies_modular_cfa_global_projection
    (pre post : ContractState) (accounts : List Address) (sender receiver : Address)
    (timestamp : Uint256) :
    pairAndFrameImplyModularCfaGlobalProjection pre post accounts sender receiver timestamp := by
  exact ?_

end Benchmark.Cases.Superfluid.RealtimeBalanceConservation
