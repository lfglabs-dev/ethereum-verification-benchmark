import Benchmark.Cases.Zama.ERC7984UpgradeableExactSource.Contract
import Benchmark.Cases.Zama.ERC7984UpgradeableExactSource.Specs

namespace Benchmark.Generated.Zama.ERC7984UpgradeableExactSource.Tasks.InitializedTransferNoBalanceRevert

set_option autoImplicit false
set_option linter.unusedVariables false

open Verity
open Verity.EVM.Uint256
open Benchmark.Cases.Zama.ERC7984UpgradeableExactSource

theorem initialized_transfer_no_balance_revert
    (sender recipient : Address) (amount : Uint256)
    (wrapperPreconditionsPassed : Bool) (s : ContractState)
    (hWrapper : wrapperPreconditionsPassed = true)
    (hFrom : (sender != zeroAddress) = true)
    (hTo : (recipient != zeroAddress) = true)
    (hInitialized : balanceIsInitialized s sender) :
    initialized_transfer_no_balance_revert_spec
      ((ERC7984UpgradeableExact.confidentialTransfer
        sender recipient amount wrapperPreconditionsPassed).run s) := by
  exact ?_

end Benchmark.Generated.Zama.ERC7984UpgradeableExactSource.Tasks.InitializedTransferNoBalanceRevert
