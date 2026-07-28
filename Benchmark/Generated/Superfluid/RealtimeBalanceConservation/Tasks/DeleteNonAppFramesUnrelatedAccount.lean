import Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Contract
import Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Specs

namespace Benchmark.Cases.Superfluid.RealtimeBalanceConservation

open Verity

theorem deleteNonApp_frames_unrelated_account (source : PinnedSourceState) (s : ContractState) (sender receiver unrelated : Address) (timestamp : Uint256) :
    deleteNonAppFramesUnrelatedAccount source s sender receiver unrelated timestamp := by
  exact ?_

end Benchmark.Cases.Superfluid.RealtimeBalanceConservation
