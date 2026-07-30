import Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Contract
import Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Specs

namespace Benchmark.Cases.Superfluid.RealtimeBalanceConservation

open Verity

theorem deleteNonApp_preserves_cfa_projection (source : PinnedSourceState) (s : ContractState) (sender receiver : Address) (timestamp : Uint256) :
    deleteNonAppPreservesCfaProjection source s sender receiver timestamp := by
  exact ?_

end Benchmark.Cases.Superfluid.RealtimeBalanceConservation
