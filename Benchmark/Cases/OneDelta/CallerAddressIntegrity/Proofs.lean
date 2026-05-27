import Benchmark.Cases.OneDelta.CallerAddressIntegrity.Specs
import Verity.Proofs.Stdlib.Automation

namespace Benchmark.Cases.OneDelta.CallerAddressIntegrity

open Verity
open Verity.EVM.Uint256

theorem delta_compose_captures_outer_caller
    (s : ContractState) :
    let s' := ((OneDeltaComposer.deltaCompose).run s).snd
    delta_compose_captures_outer_caller_spec s s' := by
  simp [delta_compose_captures_outer_caller_spec, outerCaller, outerCallerWord,
    OneDeltaComposer.deltaCompose, OneDeltaComposer.outerCallerWord, setStorage,
    Verity.bind, Bind.bind, Contract.run, ContractResult.snd, msgSender]

theorem direct_erc20_transferFrom_uses_outer_caller
    (callerAddress : Address) (s : ContractState) :
    let s' := ((OneDeltaComposer._transferFrom callerAddress).run s).snd
    erc20_caller_spec {s with sender := callerAddress} s' := by
  simp [erc20_caller_spec, erc20PullOccurred, erc20PullFrom,
    outerCallerWord, OneDeltaComposer._transferFrom,
    OneDeltaComposer.erc20TransferFromOccurred, OneDeltaComposer.erc20TransferFromWord,
    setStorage, Verity.bind, Bind.bind, Contract.run, ContractResult.snd]

theorem transfers_erc20_transferFrom_uses_outer_caller
    (callerAddress : Address) (s : ContractState) :
    let s' := ((OneDeltaComposer._transfers_transferFrom callerAddress).run s).snd
    erc20_caller_spec {s with sender := callerAddress} s' := by
  simp [erc20_caller_spec, erc20PullOccurred, erc20PullFrom,
    outerCallerWord, OneDeltaComposer._transfers_transferFrom,
    OneDeltaComposer.erc20TransferFromOccurred, OneDeltaComposer.erc20TransferFromWord,
    setStorage, Verity.bind, Bind.bind, Contract.run, ContractResult.snd]

theorem delta_compose_internal_erc20_transferFrom_uses_outer_caller
    (callerAddress : Address) (s : ContractState) :
    let s' := ((OneDeltaComposer._deltaComposeInternal_transferFrom callerAddress).run s).snd
    outerCaller s' = outerCallerWord {s with sender := callerAddress} ∧
    erc20_caller_spec {s with sender := callerAddress} s' := by
  simp [erc20_caller_spec, erc20PullOccurred, erc20PullFrom,
    outerCaller, outerCallerWord, OneDeltaComposer._deltaComposeInternal_transferFrom,
    OneDeltaComposer.outerCallerWord, OneDeltaComposer.erc20TransferFromOccurred,
    OneDeltaComposer.erc20TransferFromWord, setStorage, Verity.bind, Bind.bind,
    Contract.run, ContractResult.snd]

theorem direct_permit2_transferFrom_uses_outer_caller
    (callerAddress : Address) (s : ContractState) :
    let s' := ((OneDeltaComposer._permit2TransferFrom callerAddress).run s).snd
    permit2_caller_spec {s with sender := callerAddress} s' := by
  simp [permit2_caller_spec, permit2PullOccurred, permit2PullFrom,
    outerCallerWord, OneDeltaComposer._permit2TransferFrom,
    OneDeltaComposer.permit2TransferFromOccurred, OneDeltaComposer.permit2TransferFromWord,
    setStorage, Verity.bind, Bind.bind, Contract.run, ContractResult.snd]

theorem transfers_permit2_transferFrom_uses_outer_caller
    (callerAddress : Address) (s : ContractState) :
    let s' := ((OneDeltaComposer._transfers_permit2TransferFrom callerAddress).run s).snd
    permit2_caller_spec {s with sender := callerAddress} s' := by
  simp [permit2_caller_spec, permit2PullOccurred, permit2PullFrom,
    outerCallerWord, OneDeltaComposer._transfers_permit2TransferFrom,
    OneDeltaComposer.permit2TransferFromOccurred, OneDeltaComposer.permit2TransferFromWord,
    setStorage, Verity.bind, Bind.bind, Contract.run, ContractResult.snd]

theorem delta_compose_internal_permit2_transferFrom_uses_outer_caller
    (callerAddress : Address) (s : ContractState) :
    let s' := ((OneDeltaComposer._deltaComposeInternal_permit2TransferFrom callerAddress).run s).snd
    outerCaller s' = outerCallerWord {s with sender := callerAddress} ∧
    permit2_caller_spec {s with sender := callerAddress} s' := by
  simp [permit2_caller_spec, permit2PullOccurred, permit2PullFrom,
    outerCaller, outerCallerWord, OneDeltaComposer._deltaComposeInternal_permit2TransferFrom,
    OneDeltaComposer.outerCallerWord, OneDeltaComposer.permit2TransferFromOccurred,
    OneDeltaComposer.permit2TransferFromWord, setStorage, Verity.bind, Bind.bind,
    Contract.run, ContractResult.snd]

/- Callback entrypoints model the post-authentication continuation and take the
   decoded outer caller as `callerAddress`. The proof state below uses
   `sender := callerAddress` only as a ghost expected-caller anchor for the
   shared specs; it is not modeling the callback's real pool/lender msg.sender. -/
theorem flash_callback_erc20_transferFrom_uses_outer_caller
    (callerAddress : Address) (s : ContractState) :
    let s' := ((OneDeltaComposer.flashLoanCallbackTransferFrom callerAddress).run s).snd
    flash_callback_preserves_outer_caller_spec {s with sender := callerAddress} s' ∧
    erc20_caller_spec {s with sender := callerAddress} s' := by
  simp [flash_callback_preserves_outer_caller_spec, erc20_caller_spec,
    flashCallbackCaller, erc20PullOccurred, erc20PullFrom, outerCallerWord,
    OneDeltaComposer.flashLoanCallbackTransferFrom,
    OneDeltaComposer.flashCallbackCallerWord, OneDeltaComposer.erc20TransferFromOccurred,
    OneDeltaComposer.erc20TransferFromWord, setStorage, Verity.bind, Bind.bind,
    Contract.run, ContractResult.snd]

theorem swap_callback_permit2_transferFrom_uses_outer_caller
    (callerAddress : Address) (s : ContractState) :
    let s' := ((OneDeltaComposer.swapCallbackPermit2TransferFrom callerAddress).run s).snd
    swap_callback_preserves_outer_caller_spec {s with sender := callerAddress} s' ∧
    permit2_caller_spec {s with sender := callerAddress} s' := by
  simp [swap_callback_preserves_outer_caller_spec, permit2_caller_spec,
    swapCallbackCaller, permit2PullOccurred, permit2PullFrom, outerCallerWord,
    OneDeltaComposer.swapCallbackPermit2TransferFrom,
    OneDeltaComposer.swapCallbackCallerWord, OneDeltaComposer.permit2TransferFromOccurred,
    OneDeltaComposer.permit2TransferFromWord, setStorage, Verity.bind, Bind.bind,
    Contract.run, ContractResult.snd]

theorem v3_callback_direct_transferFrom_uses_outer_caller
    (callerAddress : Address) (s : ContractState) :
    let s' := ((OneDeltaComposer.v3SwapCallbackDirectTransferFrom callerAddress).run s).snd
    swap_callback_preserves_outer_caller_spec {s with sender := callerAddress} s' ∧
    v3_direct_caller_spec {s with sender := callerAddress} s' := by
  simp [swap_callback_preserves_outer_caller_spec,
    v3_direct_caller_spec, swapCallbackCaller,
    v3CallbackPullOccurred, v3CallbackPullFrom, outerCallerWord,
    OneDeltaComposer.v3SwapCallbackDirectTransferFrom,
    OneDeltaComposer.swapCallbackCallerWord, OneDeltaComposer.v3CallbackTransferFromOccurred,
    OneDeltaComposer.v3CallbackTransferFromWord, setStorage, Verity.bind, Bind.bind,
    Contract.run, ContractResult.snd]

theorem nested_flash_and_swap_callbacks_keep_outer_caller
    (s : ContractState) :
    let s' := ((OneDeltaComposer.allModeledPullsHarness).run s).snd
    all_path_batch_caller_integrity_spec s s' := by
  simp [all_path_batch_caller_integrity_spec, outerCaller, erc20PullOccurred,
    erc20PullFrom, permit2PullOccurred, permit2PullFrom, flashCallbackCaller,
    swapCallbackCaller, v3CallbackPullOccurred, v3CallbackPullFrom, outerCallerWord,
    OneDeltaComposer.allModeledPullsHarness, OneDeltaComposer.outerCallerWord,
    OneDeltaComposer.erc20TransferFromOccurred, OneDeltaComposer.erc20TransferFromWord,
    OneDeltaComposer.permit2TransferFromOccurred, OneDeltaComposer.permit2TransferFromWord,
    OneDeltaComposer.flashCallbackCallerWord, OneDeltaComposer.swapCallbackCallerWord,
    OneDeltaComposer.v3CallbackTransferFromOccurred, OneDeltaComposer.v3CallbackTransferFromWord,
    setStorage, Verity.bind, Bind.bind, Contract.run, ContractResult.snd, msgSender]

end Benchmark.Cases.OneDelta.CallerAddressIntegrity
