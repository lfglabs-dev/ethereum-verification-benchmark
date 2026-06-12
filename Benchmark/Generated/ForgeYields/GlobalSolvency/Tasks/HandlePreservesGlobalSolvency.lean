import Benchmark.Cases.ForgeYields.GlobalSolvency.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.ForgeYields.GlobalSolvency

open Verity
open Verity.EVM.Uint256

theorem handle_preserves_global_solvency
    (assetsIn lockAssets : Uint256) (s : ContractState)
    (hActive : s.storage 3 = 0)
    (hAssetNoOverflow : (s.storage 0).val + assetsIn.val < Verity.Core.Uint256.modulus)
    (hBufferNoOverflow : (s.storage 1).val + assetsIn.val < Verity.Core.Uint256.modulus)
    (hLockedNoOverflow : (s.storage 2).val + lockAssets.val < Verity.Core.Uint256.modulus)
    (hLockLeBufferIn : lockAssets.val <= (s.storage 1).val + assetsIn.val) :
    let s' := ((TokenGateway.handle assetsIn lockAssets).run s).snd
    handle_preserves_global_solvency_spec s s' := by
  exact ?_

end Benchmark.Cases.ForgeYields.GlobalSolvency
