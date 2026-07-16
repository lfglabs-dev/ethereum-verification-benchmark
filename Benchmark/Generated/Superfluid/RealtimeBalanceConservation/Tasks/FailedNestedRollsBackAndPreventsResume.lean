import Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Contract
import Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Specs

namespace Benchmark.Cases.Superfluid.RealtimeBalanceConservation

open Verity

theorem failedNested_rolls_back_and_prevents_resume {α β γ : Type}
    (outerPrefix : Contract α) (nested : α → Contract β)
    (outerResume : α → β → Contract γ) :
    failedNestedRollsBackAndPreventsResume outerPrefix nested outerResume := by
  exact ?_

end Benchmark.Cases.Superfluid.RealtimeBalanceConservation
