import Contracts.Common

namespace Benchmark.Cases.ERC4337.EntryPointInvariant

open Verity hiding pure bind

/-!
# EntryPoint selector and topic constants

These constants are intentionally derived from canonical Solidity signature
strings with Verity's kernel-computable Keccak engine. The `*_legacyHex_eq`
lemmas keep the old hand-transcribed values as proof obligations instead of
authoritative definitions.
-/

def selectorShift : Nat := 2 ^ 224

def selectorFromSignature (sig : String) : Nat :=
  (Verity.keccak256_lit sig).val / selectorShift

def entryPointHandleOpsSignature : String :=
  "handleOps(PackedUserOperation[],address)"

def projectedHandleOpsSignature : String :=
  "handleOps(address,address,uint256,uint256,address,uint256,uint256)"

def userOperationEventSignature : String :=
  "UserOperationEvent(bytes32,address,address,uint256,bool,uint256,uint256)"

def accountDeployedEventSignature : String :=
  "AccountDeployed(bytes32,address,address,address)"

def userOperationRevertReasonEventSignature : String :=
  "UserOperationRevertReason(bytes32,address,uint256,bytes)"

/-- Upstream EntryPoint v0.9 `handleOps(PackedUserOperation[],address)`. -/
def entryPointHandleOpsSelector : Uint256 :=
  Verity.Core.Uint256.ofNat (selectorFromSignature entryPointHandleOpsSignature)

/-- Dispatcher selector for the flattened Verity projection in `EntryPointV09`. -/
def projectedHandleOpsSelector : Uint256 :=
  Verity.Core.Uint256.ofNat (selectorFromSignature projectedHandleOpsSignature)

def userOperationEventTopic0 : Uint256 :=
  Verity.keccak256_lit userOperationEventSignature

def accountDeployedTopic0 : Uint256 :=
  Verity.keccak256_lit accountDeployedEventSignature

def userOperationRevertReasonTopic0 : Uint256 :=
  Verity.keccak256_lit userOperationRevertReasonEventSignature

set_option maxRecDepth 100000 in
theorem userOperationEventTopic0_legacyHex_eq :
    (keccakString "UserOperationEvent(bytes32,address,address,uint256,bool,uint256,uint256)").val =
      0x49628fd1471006c1482da88028e9ce4dbb080b815c9b0344d39e5a8e6ec1419f := by
  rfl

set_option maxRecDepth 100000 in
theorem accountDeployedTopic0_legacyHex_eq :
    (keccakString "AccountDeployed(bytes32,address,address,address)").val =
      0xd51a9c61267aa6196961883ecf5ff2da6619c37dac0fa92122513fb32c032d2d := by
  rfl

set_option maxRecDepth 100000 in
theorem userOperationRevertReasonTopic0_legacyHex_eq :
    (keccakString "UserOperationRevertReason(bytes32,address,uint256,bytes)").val =
      0x1c4fada7374c0a9ee8841fc38afe82932dc0f8e69012e927f061a8bae611a201 := by
  rfl

end Benchmark.Cases.ERC4337.EntryPointInvariant
