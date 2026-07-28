import Benchmark.Cases.Zama.ERC7984UpgradeableExactSource.Contract
import Benchmark.Cases.Zama.ERC7984UpgradeableExactSource.Specs

namespace Benchmark.Generated.Zama.ERC7984UpgradeableExactSource.Tasks.InitializedInsufficientTransferZero

set_option autoImplicit false
set_option linter.unusedVariables false

open Verity
open Verity.EVM.Uint256
open Benchmark.Cases.Zama.ERC7984UpgradeableExactSource

theorem initialized_insufficient_transfer_zero
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
    (hInsufficient : ¬ (balanceOf s sender >= amount)) :
    initialized_insufficient_transfer_zero_spec sender recipient s
      ((ERC7984UpgradeableExact.confidentialTransferSlice
        sender recipient amount wrapperPreconditionsPassed).run s) := by
  exact ?_

end Benchmark.Generated.Zama.ERC7984UpgradeableExactSource.Tasks.InitializedInsufficientTransferZero
