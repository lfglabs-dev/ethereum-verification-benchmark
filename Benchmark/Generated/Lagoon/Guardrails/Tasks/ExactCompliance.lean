import Benchmark.Cases.Lagoon.Guardrails.Specs

namespace Benchmark.Generated.Lagoon.Guardrails.Tasks

open Benchmark.Cases.Lagoon.Guardrails
open Verity
open Verity.EVM

theorem exact_compliance_task
    (currentPps nextPps timePast upperRate : Uint256)
    (lowerRate : Verity.Core.Int256) :
    exactComplianceSpec currentPps nextPps timePast upperRate lowerRate := by
  exact ?_

end Benchmark.Generated.Lagoon.Guardrails.Tasks
