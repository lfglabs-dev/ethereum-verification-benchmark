import Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Contract
import Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Specs

namespace Benchmark.Cases.Superfluid.RealtimeBalanceConservation

open Verity

theorem deleteNonApp_preserves_pair_net_flow_rate (source : PinnedSourceState) (s : ContractState) (sender receiver : Address) (timestamp : Uint256) :
    deleteNonAppPreservesPairNetFlowRate source s sender receiver timestamp := by
  exact ?_

end Benchmark.Cases.Superfluid.RealtimeBalanceConservation
