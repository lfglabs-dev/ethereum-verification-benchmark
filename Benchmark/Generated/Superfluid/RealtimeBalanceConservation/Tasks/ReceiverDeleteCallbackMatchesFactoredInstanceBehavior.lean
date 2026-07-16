import Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Contract
import Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Specs

namespace Benchmark.Cases.Superfluid.RealtimeBalanceConservation

open Verity

theorem receiverDeleteCallback_matches_factored_instance_behavior
    (source : PinnedSourceState) (s : ContractState) (sender receiver : Address)
    (flowRate liquidationPeriod minimumDeposit operationTimestamp : Uint256) :
    receiverDeleteCallbackFactoredInstanceBehavior source s sender receiver flowRate
      liquidationPeriod minimumDeposit operationTimestamp := by
  exact ?_

end Benchmark.Cases.Superfluid.RealtimeBalanceConservation
