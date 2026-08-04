import Benchmark.Cases.Velora.BridgeStaking.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Velora.BridgeStaking

open Verity
open Verity.EVM.Uint256

/--
Reference: Benchmark.Cases.Velora.BridgeStaking.handleV3AcrossMessage_preserves_allocated
The reference module proves conservation for the complete modeled transition. The
transition validates the callback amount against the selected stored amount after
beneficiary-sentinel initialization. `depositResult` selects external seVLR success
or catch, and the Boolean transfer outcomes model each catch/rescue SafeTransferLib
call. Arithmetic, transfer, and explicit-guard failures atomically revert.
-/
theorem handleV3AcrossMessage_preserves_allocated
    (key vlrAmount wethAmount minBptAmount : Uint256)
    (beneficiary : Address)
    (isVlr : Bool)
    (receivedAmount depositResult : Uint256)
    (vlrTransferSuccess wethTransferSuccess : Bool)
    (s : ContractState) :
    handleV3AcrossMessage_preserves_spec key vlrAmount wethAmount minBptAmount
      beneficiary isVlr receivedAmount depositResult vlrTransferSuccess
      wethTransferSuccess s := by
  exact ?_

end Benchmark.Cases.Velora.BridgeStaking
