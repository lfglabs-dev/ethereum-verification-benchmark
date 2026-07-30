import Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Contract
import Benchmark.Cases.Superfluid.RealtimeBalanceConservation.Specs

namespace Benchmark.Cases.Superfluid.RealtimeBalanceConservation

open Verity

theorem successfulOneLevel_components_compose {α β γ : Type}
    (outerPrefix : Contract α) (nested : α → Contract β)
    (outerResume : α → β → Contract γ) (accounts : List Address) (timestamp : Uint256) :
    successfulOneLevelComponentsCompose outerPrefix nested outerResume accounts timestamp := by
  exact ?_

end Benchmark.Cases.Superfluid.RealtimeBalanceConservation
