import Benchmark.Cases.Zama.ERC7984UpgradeableExactSource.Contract
import Benchmark.Cases.Zama.ERC7984UpgradeableExactSource.Specs

namespace Benchmark.Generated.Zama.ERC7984UpgradeableExactSource.Tasks.InitializedTransferPairConservation

set_option autoImplicit false
set_option linter.unusedVariables false

open Verity
open Verity.EVM.Uint256
open Benchmark.Cases.Zama.ERC7984UpgradeableExactSource

theorem initialized_transfer_pair_conservation
    (sender recipient : Address) (amount : Uint256)
    (wrapperPreconditionsPassed : Bool) (s : ContractState)
    (hWrapper : wrapperPreconditionsPassed = true)
    (hFrom : (sender != zeroAddress) = true)
    (hTo : (recipient != zeroAddress) = true)
    (hInitialized : balanceIsInitialized s sender)
    (hAmount64 : amount < UINT64_MOD)
    (hSender64 : balanceOf s sender < UINT64_MOD)
    (hRecipient64 : balanceOf s recipient < UINT64_MOD)
    (hDistinct : sender ≠ recipient)
    (hRecipientNoWrap :
      balanceOf s recipient + selectedTransferAmount s sender amount < UINT64_MOD) :
    let s' := ((ERC7984UpgradeableExact.confidentialTransferSlice
      sender recipient amount wrapperPreconditionsPassed).run s).snd
    initialized_transfer_pair_conservation_spec sender recipient s s' := by
  exact ?_

end Benchmark.Generated.Zama.ERC7984UpgradeableExactSource.Tasks.InitializedTransferPairConservation
