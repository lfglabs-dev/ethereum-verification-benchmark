import Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Contract
import Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Specs

namespace Benchmark.Cases.Superfluid.RealtimeBalanceConservation

open Verity

theorem updateNonApp_preserves_cfa_projection (source : PinnedSourceState) (s : ContractState) (sender receiver : Address) (flowRate liquidationPeriod minimumDeposit timestamp : Uint256) :
    updateNonAppPreservesCfaProjection source s sender receiver flowRate liquidationPeriod minimumDeposit timestamp := by
  exact ?_

end Benchmark.Cases.Superfluid.RealtimeBalanceConservation
