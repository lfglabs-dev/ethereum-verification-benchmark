import Benchmark.Cases.ForgeYields.GlobalSolvency.Specs

namespace Benchmark.Cases.ForgeYields.GlobalSolvency

open Verity
open Verity.EVM.Uint256

theorem report_preserves_global_solvency
    (s : ContractState) :
    let s' := ((TokenGateway.report).run s).snd
    report_preserves_global_solvency_spec s s' := by
  exact ?_

end Benchmark.Cases.ForgeYields.GlobalSolvency
