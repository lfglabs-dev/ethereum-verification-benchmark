import Benchmark.Cases.Zama.ERC7984UpgradeableExactSource.Contract
import Benchmark.Cases.Zama.ERC7984UpgradeableExactSource.Specs

namespace Benchmark.Generated.Zama.ERC7984UpgradeableExactSource.Tasks.UninitializedSenderRevertsWithoutWrites

set_option autoImplicit false
set_option linter.unusedVariables false

open Verity
open Verity.EVM.Uint256
open Benchmark.Cases.Zama.ERC7984UpgradeableExactSource

theorem uninitialized_sender_reverts_without_writes
    (sender recipient : Address) (amount : Uint256)
    (wrapperPreconditionsPassed : Bool) (s : ContractState)
    (hWrapper : wrapperPreconditionsPassed = true)
    (hFrom : (sender != zeroAddress) = true)
    (hTo : (recipient != zeroAddress) = true)
    (hAmount64 : amount < UINT64_MOD)
    (hUninitialized : s.storageMap 2 sender = 0) :
    uninitialized_sender_reverts_without_writes_spec
      ((ERC7984UpgradeableExact.confidentialTransferSlice
        sender recipient amount wrapperPreconditionsPassed).run s) s := by
  exact ?_

end Benchmark.Generated.Zama.ERC7984UpgradeableExactSource.Tasks.UninitializedSenderRevertsWithoutWrites
