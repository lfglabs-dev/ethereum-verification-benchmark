import Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Contract
import Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Specs

namespace Benchmark.Cases.Superfluid.RealtimeBalanceConservation

open Verity

theorem createNonApp_preserves_pair_net_flow_rate (source : PinnedSourceState) (s : ContractState) (sender receiver : Address) (flowRate liquidationPeriod minimumDeposit timestamp : Uint256) :
    createNonAppPreservesPairNetFlowRate source s sender receiver flowRate liquidationPeriod minimumDeposit timestamp := by
  exact ?_

end Benchmark.Cases.Superfluid.RealtimeBalanceConservation
