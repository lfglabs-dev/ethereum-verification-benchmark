import Benchmark.Cases.ForgeYields.GlobalSolvency.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.ForgeYields.GlobalSolvency

open Verity
open Verity.EVM.Uint256

theorem deposit_preserves_global_solvency
    (assets : Uint256) (s : ContractState)
    (hActive : s.storage 3 = 0)
    (hAssetNoOverflow : (s.storage 0).val + assets.val < Verity.Core.Uint256.modulus)
    (hBufferNoOverflow : (s.storage 1).val + assets.val < Verity.Core.Uint256.modulus) :
    let s' := ((TokenGateway.deposit assets).run s).snd
    deposit_preserves_global_solvency_spec s s' := by
  exact ?_

end Benchmark.Cases.ForgeYields.GlobalSolvency
