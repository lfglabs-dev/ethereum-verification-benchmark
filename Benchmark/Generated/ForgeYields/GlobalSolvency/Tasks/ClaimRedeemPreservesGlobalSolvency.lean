import Benchmark.Cases.ForgeYields.GlobalSolvency.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.ForgeYields.GlobalSolvency

open Verity
open Verity.EVM.Uint256

theorem claimRedeem_preserves_global_solvency
    (assets : Uint256) (s : ContractState)
    (hAssetsLeLocked : assets.val <= (s.storage 2).val)
    (hAssetsLeAsset : assets.val <= (s.storage 0).val) :
    let s' := ((TokenGateway.claimRedeem assets).run s).snd
    claimRedeem_preserves_global_solvency_spec s s' := by
  exact ?_

end Benchmark.Cases.ForgeYields.GlobalSolvency
