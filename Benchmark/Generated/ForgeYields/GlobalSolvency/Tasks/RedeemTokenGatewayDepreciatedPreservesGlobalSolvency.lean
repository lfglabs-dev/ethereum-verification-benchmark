import Benchmark.Cases.ForgeYields.GlobalSolvency.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.ForgeYields.GlobalSolvency

open Verity
open Verity.EVM.Uint256

theorem redeemTokenGatewayDepreciated_preserves_global_solvency
    (assets : Uint256) (s : ContractState)
    (hDep : s.storage 3 != 0)
    (hAssetsLeAsset : assets.val <= (s.storage 0).val) :
    let s' := ((TokenGateway.redeemTokenGatewayDepreciated assets).run s).snd
    redeemTokenGatewayDepreciated_preserves_global_solvency_spec s s' := by
  exact ?_

end Benchmark.Cases.ForgeYields.GlobalSolvency
