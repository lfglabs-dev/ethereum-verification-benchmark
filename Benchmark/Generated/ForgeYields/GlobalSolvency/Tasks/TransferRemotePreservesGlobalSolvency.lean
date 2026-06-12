import Benchmark.Cases.ForgeYields.GlobalSolvency.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.ForgeYields.GlobalSolvency

open Verity
open Verity.EVM.Uint256

theorem transferRemote_preserves_global_solvency
    (assets : Uint256) (s : ContractState)
    (hActive : s.storage 3 = 0)
    (hAssetsLeBuffer : assets.val <= (s.storage 1).val)
    (hAssetsLeAsset : assets.val <= (s.storage 0).val) :
    let s' := ((TokenGateway.transferRemote assets).run s).snd
    transferRemote_preserves_global_solvency_spec s s' := by
  exact ?_

end Benchmark.Cases.ForgeYields.GlobalSolvency
