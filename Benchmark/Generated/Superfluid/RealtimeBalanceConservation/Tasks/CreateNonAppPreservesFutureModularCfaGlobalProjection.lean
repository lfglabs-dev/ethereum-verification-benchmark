import Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Contract
import Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Specs

namespace Benchmark.Cases.Superfluid.RealtimeBalanceConservation

open Verity

theorem createNonApp_preserves_future_modular_cfa_global_projection
    (source : PinnedSourceState) (s : ContractState) (accounts : List Address)
    (sender receiver : Address)
    (flowRate liquidationPeriod minimumDeposit operationTimestamp tau : Uint256) :
    createNonAppPreservesFutureModularCfaGlobalProjection source s accounts sender receiver
      flowRate liquidationPeriod minimumDeposit operationTimestamp tau := by
  exact ?_

end Benchmark.Cases.Superfluid.RealtimeBalanceConservation
