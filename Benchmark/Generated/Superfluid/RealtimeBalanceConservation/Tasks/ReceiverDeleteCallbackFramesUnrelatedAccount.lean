import Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Contract
import Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Specs

namespace Benchmark.Cases.Superfluid.RealtimeBalanceConservation

open Verity

theorem receiverDeleteCallback_frames_unrelated_account (source : PinnedSourceState) (s : ContractState) (sender receiver unrelated : Address) (flowRate liquidationPeriod minimumDeposit timestamp : Uint256) :
    receiverDeleteCallbackFramesUnrelatedAccount source s sender receiver unrelated flowRate liquidationPeriod minimumDeposit timestamp := by
  exact ?_

end Benchmark.Cases.Superfluid.RealtimeBalanceConservation
