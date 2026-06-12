import Benchmark.Cases.Lagoon.Guardrails.Specs
import Benchmark.Grindset

namespace Benchmark.Generated.Lagoon.Guardrails.Tasks

open Benchmark.Cases.Lagoon.Guardrails
open Verity
open Verity.EVM

theorem negative_variation_bounded_task
    (currentPps nextPps timePast upperRate : Uint256)
    (lowerRate : Verity.Core.Int256) :
    negativeVariationBoundedSpec currentPps nextPps timePast upperRate lowerRate := by
  exact ?_

end Benchmark.Generated.Lagoon.Guardrails.Tasks
