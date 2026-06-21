import Benchmark.Cases.ERC4337.EntryPointInvariant.Trace
import Benchmark.Cases.ERC4337.EntryPointInvariant.Yoav

namespace Benchmark.Cases.ERC4337.EntryPointInvariant

open Verity hiding pure bind
open Verity.EVM.Uint256
open Contracts

/-!
# Real EntryPoint ABI boundary

This module makes the boundary used by the differential harness explicit in the
proof tree:

```
handleOps(PackedUserOperation[] calldata ops, address beneficiary)
  -> decoded EntryPoint batch model
  -> current simplified/proof projection
```

The byte-level calldata decoder is inserted into the generated Yul artifact by
`differential/run.sh` and is exercised by the Foundry suite through the exact
upstream ABI selector. This file records the semantic object that decoder must
produce: a decoded batch plus beneficiary, where the batch is the same
`PackedUserOperation` list consumed by `Trace.lean` and `Yoav.lean`.
-/

/-- Canonical selector for
`handleOps((address,uint256,bytes,bytes,bytes32,uint256,bytes32,bytes,bytes)[],address)`.
This is the Solidity ABI spelling of
`handleOps(PackedUserOperation[] calldata ops, address beneficiary)`. -/
def HANDLE_OPS_PACKED_USER_OPERATION_ARRAY_SELECTOR : Nat := 0x765e827f

/-- The decoded semantic payload of the real Solidity ABI call. -/
structure HandleOpsAbiCall where
  selector    : Nat
  ops         : List PackedUserOperation
  beneficiary : Address
  deriving Repr

/-- The exact ABI selector is part of the trusted boundary contract. -/
def hasUpstreamHandleOpsSelector (call : HandleOpsAbiCall) : Bool :=
  decide (call.selector = HANDLE_OPS_PACKED_USER_OPERATION_ARRAY_SELECTOR)

/-- Decode acceptance predicate used by the ABI-backed path. -/
def abiCallAccepted (call : HandleOpsAbiCall) : Bool :=
  hasUpstreamHandleOpsSelector call

/-- Projection from the decoded ABI payload to the proof model. The projection
is deliberately secondary: it consumes the already-decoded upstream call rather
than replacing the ABI. -/
def abiCallToBatch (call : HandleOpsAbiCall) : List PackedUserOperation :=
  call.ops

/-- ABI-backed EntryPoint semantics: reject non-upstream selectors, otherwise
run the decoded batch through the existing validation/execution model. -/
def handleOpsFromAbi
    (call : HandleOpsAbiCall)
    (table : Nonce2DTable)
    (accountApprovals : List Bool)
    : Option (Nonce2DTable × Trace) :=
  if abiCallAccepted call then
    handleOpsMulti (abiCallToBatch call) table accountApprovals
  else
    none

/-- The executable trace produced by the ABI-backed path. -/
def handleOpsAbiTrace
    (call : HandleOpsAbiCall)
    (table : Nonce2DTable)
    (accountApprovals : List Bool) : Trace :=
  match handleOpsFromAbi call table accountApprovals with
  | some (_, trace) => trace
  | none => []

theorem handleOpsFromAbi_refines_decoded_batch
    (call : HandleOpsAbiCall) (table : Nonce2DTable)
    (accountApprovals : List Bool)
    (hSelector : abiCallAccepted call = true) :
    handleOpsFromAbi call table accountApprovals =
      handleOpsMulti call.ops table accountApprovals := by
  unfold handleOpsFromAbi abiCallToBatch
  simp [hSelector]

theorem handleOpsAbiTrace_refines_handleOpsTrace
    (call : HandleOpsAbiCall) (table : Nonce2DTable)
    (accountApprovals : List Bool)
    (hSelector : abiCallAccepted call = true) :
    handleOpsAbiTrace call table accountApprovals =
      handleOpsTrace call.ops table accountApprovals := by
  unfold handleOpsAbiTrace handleOpsTrace
  rw [handleOpsFromAbi_refines_decoded_batch call table accountApprovals hSelector]
  cases handleOpsMulti call.ops table accountApprovals <;> rfl

/-- ABI-backed Yoav theorem: for every op received through the real ABI, the
translated EntryPoint path records exactly one execution event iff the decoded
batch validated and that op carries non-empty calldata. Callee behavior remains
inside the ECM assumptions used by `Trace.lean`/`Yoav.lean`. -/
theorem abi_backed_yoav_counting_biconditional
    (call : HandleOpsAbiCall)
    (hSelector : abiCallAccepted call = true)
    (hDistinct : List.Pairwise
      (fun a b => ¬ (a.sender = b.sender ∧ a.callData = b.callData)) call.ops)
    (table : Nonce2DTable) (approvals : List Bool)
    (i : Nat) (hi : i < call.ops.length) :
    countExecCalls (handleOpsAbiTrace call table approvals)
      call.ops[i].sender call.ops[i].callData = 1 ↔
    batchValidated call.ops table approvals = true ∧
    opExecutable call.ops i hi = true := by
  rw [handleOpsAbiTrace_refines_handleOpsTrace call table approvals hSelector]
  exact yoav_counting_biconditional call.ops hDistinct table approvals i hi

end Benchmark.Cases.ERC4337.EntryPointInvariant
