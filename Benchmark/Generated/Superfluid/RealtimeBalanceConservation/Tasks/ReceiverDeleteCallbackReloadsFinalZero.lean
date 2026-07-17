import Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Contract
import Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Specs

namespace Benchmark.Cases.Superfluid.RealtimeBalanceConservation

open Verity

theorem receiverDeleteCallback_reloads_final_zero (source : PinnedSourceState) (s : ContractState) (sender receiver : Address) (flowRate liquidationPeriod minimumDeposit timestamp : Uint256) :
    receiverDeleteCallbackReloadsFinalZero source s sender receiver flowRate liquidationPeriod minimumDeposit timestamp := by
  exact ?_

end Benchmark.Cases.Superfluid.RealtimeBalanceConservation
