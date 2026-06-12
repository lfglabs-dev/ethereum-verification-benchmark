import Benchmark.Cases.ForgeYields.GlobalSolvency.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.ForgeYields.GlobalSolvency

open Verity
open Verity.EVM.Uint256

theorem requestRedeem_preserves_global_solvency
    (assets : Uint256) (s : ContractState)
    (hActive : s.storage 3 = 0)
    (hAssetsLeBuffer : assets.val <= (s.storage 1).val)
    (hLockedNoOverflow : (s.storage 2).val + assets.val < Verity.Core.Uint256.modulus) :
    let s' := ((TokenGateway.requestRedeem assets).run s).snd
    requestRedeem_preserves_global_solvency_spec s s' := by
  exact ?_

end Benchmark.Cases.ForgeYields.GlobalSolvency
