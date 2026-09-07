import Benchmark.Cases.Tydro.PositionAccountFloorAuthority.Specs
import Verity.Proofs.Stdlib.Automation
import Benchmark.Grindset

namespace Benchmark.Cases.Tydro.PositionAccountFloorAuthority

open Verity
open Verity.EVM.Uint256

/-- Successful lifecycle consumption proves identity, relayer, nonce, and owner authority. -/
theorem lifecycle_success_requires_owner_authority
    (signedAccount signedOwner signedPool signedSupply signedBorrow authorizedCaller : Address)
    (signedNonce deadline : Uint256) (recoveredSigner : Address) (s : ContractState) :
    lifecycle_authority_spec signedAccount signedOwner signedPool signedSupply signedBorrow
      authorizedCaller signedNonce deadline recoveredSigner s := by
  exact ?_

end Benchmark.Cases.Tydro.PositionAccountFloorAuthority
