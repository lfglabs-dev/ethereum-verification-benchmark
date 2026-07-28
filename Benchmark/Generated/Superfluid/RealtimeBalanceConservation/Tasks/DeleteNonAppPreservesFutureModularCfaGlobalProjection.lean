import Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Contract
import Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Specs

namespace Benchmark.Cases.Superfluid.RealtimeBalanceConservation

open Verity

theorem deleteNonApp_preserves_future_modular_cfa_global_projection
    (source : PinnedSourceState) (s : ContractState) (accounts : List Address)
    (sender receiver : Address) (operationTimestamp tau : Uint256) :
    deleteNonAppPreservesFutureModularCfaGlobalProjection source s accounts sender receiver
      operationTimestamp tau := by
  exact ?_

end Benchmark.Cases.Superfluid.RealtimeBalanceConservation
