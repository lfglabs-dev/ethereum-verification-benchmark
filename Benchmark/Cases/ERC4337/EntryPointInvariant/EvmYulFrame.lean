import Benchmark.Cases.ERC4337.EntryPointInvariant.Frame
import Verity.EVM.Frame

namespace Benchmark.Cases.ERC4337.EntryPointInvariant.EvmYulFrame

/-!
# EvmYul-side frame adapters

The EVM `CALL` frame model and preservation lemmas now live upstream in
`Verity.EVM.Frame`. This module keeps the benchmark-local namespace stable
while consuming those upstream definitions directly.
-/

abbrev Word := Verity.Core.Uint256
abbrev Address := Verity.EVM.Frame.Address
abbrev CallerFrame := Verity.EVM.Frame.CallerFrame
abbrev CalleeResult := Verity.EVM.Frame.CalleeResult

abbrev applyCallToCaller := Verity.EVM.Frame.applyCallToCaller

theorem external_call_preserves_caller_storage
    (caller : CallerFrame) (outOff outSize : Nat) (callee : CalleeResult)
    (slotIdx : Nat) :
    (applyCallToCaller caller outOff outSize callee).storageMap slotIdx =
      caller.storageMap slotIdx :=
  Verity.EVM.Frame.external_call_preserves_caller_storage
    caller outOff outSize callee slotIdx

theorem external_call_preserves_caller_transient_storage
    (caller : CallerFrame) (outOff outSize : Nat) (callee : CalleeResult)
    (slotIdx : Nat) :
    (applyCallToCaller caller outOff outSize callee).transientStorage slotIdx =
      caller.transientStorage slotIdx :=
  Verity.EVM.Frame.external_call_preserves_caller_transient_storage
    caller outOff outSize callee slotIdx

theorem external_call_preserves_caller_memory_outside_output_buffer
    (caller : CallerFrame) (outOff outSize : Nat) (callee : CalleeResult)
    (i : Nat) (hOutside : ¬ (outOff ≤ i ∧ i < outOff + outSize)) :
    (applyCallToCaller caller outOff outSize callee).memory i =
      caller.memory i :=
  Verity.EVM.Frame.external_call_preserves_caller_memory_outside_output_buffer
    caller outOff outSize callee i hOutside

theorem external_call_preserves_caller_memory
    (caller : CallerFrame) (outOff outSize : Nat) (callee : CalleeResult)
    (regionLo regionHi : Nat)
    (hDisj : outOff + outSize ≤ regionLo ∨ regionHi ≤ outOff)
    (i : Nat) (hLo : regionLo ≤ i) (hHi : i < regionHi) :
    (applyCallToCaller caller outOff outSize callee).memory i =
      caller.memory i :=
  Verity.EVM.Frame.external_call_preserves_caller_memory
    caller outOff outSize callee regionLo regionHi hDisj i hLo hHi

theorem external_calls_preserve_caller_storage
    (caller : CallerFrame)
    (calls : List (Nat × Nat × CalleeResult))
    (slotIdx : Nat) :
    (calls.foldl
      (fun s c => applyCallToCaller s c.1 c.2.1 c.2.2) caller).storageMap slotIdx =
    caller.storageMap slotIdx :=
  Verity.EVM.Frame.external_calls_preserve_caller_storage caller calls slotIdx

theorem external_calls_preserve_caller_transient_storage
    (caller : CallerFrame)
    (calls : List (Nat × Nat × CalleeResult))
    (slotIdx : Nat) :
    (calls.foldl
      (fun s c => applyCallToCaller s c.1 c.2.1 c.2.2) caller).transientStorage slotIdx =
    caller.transientStorage slotIdx :=
  Verity.EVM.Frame.external_calls_preserve_caller_transient_storage caller calls slotIdx

theorem external_calls_preserve_caller_memory_in_disjoint_region
    (caller : CallerFrame)
    (regionLo regionHi : Nat)
    (calls : List (Nat × Nat × CalleeResult))
    (hAllDisj : ∀ c ∈ calls,
      c.1 + c.2.1 ≤ regionLo ∨ regionHi ≤ c.1)
    (i : Nat) (hLo : regionLo ≤ i) (hHi : i < regionHi) :
    (calls.foldl
      (fun s c => applyCallToCaller s c.1 c.2.1 c.2.2) caller).memory i =
    caller.memory i :=
  Verity.EVM.Frame.external_calls_preserve_caller_memory_in_disjoint_region
    caller regionLo regionHi calls hAllDisj i hLo hHi

end Benchmark.Cases.ERC4337.EntryPointInvariant.EvmYulFrame
