import Benchmark.Cases.UnlinkXyz.Pool.Specs
import Benchmark.Cases.UnlinkXyz.Pool.InternalLazyIMT
import Benchmark.Cases.UnlinkXyz.Pool.State
import Benchmark.Cases.UnlinkXyz.Pool.Contract
import Benchmark.Cases.UnlinkXyz.Pool.VerifierRouter
import Benchmark.Cases.UnlinkXyz.Pool.Proofs

namespace Benchmark.Cases.UnlinkXyz.Pool

open Compiler.CompilationModel

private def uintArray : ParamType :=
  ParamType.array ParamType.uint256

private def noteParam : ParamType :=
  ParamType.tuple [ParamType.uint256, ParamType.address, ParamType.uint256]

private def ciphertextParam : ParamType :=
  ParamType.tuple [
    ParamType.uint256,
    ParamType.fixedArray ParamType.uint256 3
  ]

private def ciphertextArray : ParamType :=
  ParamType.array ciphertextParam

private def tokenPermissionsParam : ParamType :=
  ParamType.tuple [ParamType.address, ParamType.uint256]

private def permitTransferFromParam : ParamType :=
  ParamType.tuple [tokenPermissionsParam, ParamType.uint256, ParamType.uint256]

private def eventParamEq (a b : EventParam) : Bool :=
  a.name == b.name && a.ty == b.ty && a.kind == b.kind

private def eventDefEq (name : String) (params : List EventParam) (eventDef : EventDef) : Bool :=
  eventDef.name == name &&
    eventDef.params.length == params.length &&
    (eventDef.params.zip params).all (fun (actual, expected) => eventParamEq actual expected)

private def hasEvent (name : String) (params : List EventParam) : Bool :=
  UnlinkPool.spec.events.any (eventDefEq name params)

private def hasRouterEvent (name : String) (params : List EventParam) : Bool :=
  VerifierRouter.spec.events.any (eventDefEq name params)

private def hasRouterEntrypoint (name : String) : Bool :=
  VerifierRouter.spec.functions.any (fun fn => fn.name == name && !fn.isInternal)

private def stmtIsInternalCall (callee : String) : Stmt → Bool
  | Stmt.internalCall name _ => name == callee || name == s!"internal_{callee}"
  | Stmt.internalCallAssign _ name _ => name == callee || name == s!"internal_{callee}"
  | _ => false

private def stmtListHasInternalCall (callee : String) (body : List Stmt) : Bool :=
  body.any (stmtIsInternalCall callee)

def unlinkPoolEventMetadataMatchesSource : Bool :=
  hasEvent "Deposited" [
    { name := "depositor", ty := ParamType.address, kind := EventParamKind.indexed },
    { name := "newRoot", ty := ParamType.uint256, kind := EventParamKind.unindexed },
    { name := "startIndex", ty := ParamType.uint256, kind := EventParamKind.unindexed },
    { name := "notes", ty := ParamType.array noteParam, kind := EventParamKind.unindexed },
    { name := "ciphertexts", ty := ciphertextArray, kind := EventParamKind.unindexed }
  ] &&
  hasEvent "Transferred" [
    { name := "newRoot", ty := ParamType.uint256, kind := EventParamKind.indexed },
    { name := "startIndex", ty := ParamType.uint256, kind := EventParamKind.unindexed },
    { name := "commitments", ty := uintArray, kind := EventParamKind.unindexed },
    { name := "nullifierHashes", ty := uintArray, kind := EventParamKind.unindexed },
    { name := "ciphertexts", ty := ciphertextArray, kind := EventParamKind.unindexed }
  ] &&
  hasEvent "Withdrawn" [
    { name := "to", ty := ParamType.address, kind := EventParamKind.indexed },
    { name := "note", ty := noteParam, kind := EventParamKind.unindexed },
    { name := "newRoot", ty := ParamType.uint256, kind := EventParamKind.indexed },
    { name := "startIndex", ty := ParamType.uint256, kind := EventParamKind.unindexed },
    { name := "commitments", ty := uintArray, kind := EventParamKind.unindexed },
    { name := "nullifierHashes", ty := uintArray, kind := EventParamKind.unindexed },
    { name := "ciphertexts", ty := ciphertextArray, kind := EventParamKind.unindexed }
  ] &&
  hasEvent "EmergencyWithdrawn" [
    { name := "to", ty := ParamType.address, kind := EventParamKind.indexed },
    { name := "note", ty := noteParam, kind := EventParamKind.unindexed },
    { name := "newRoot", ty := ParamType.uint256, kind := EventParamKind.indexed },
    { name := "startIndex", ty := ParamType.uint256, kind := EventParamKind.unindexed },
    { name := "commitments", ty := uintArray, kind := EventParamKind.unindexed },
    { name := "nullifierHashes", ty := uintArray, kind := EventParamKind.unindexed },
    { name := "ciphertexts", ty := ciphertextArray, kind := EventParamKind.unindexed }
  ] &&
  hasEvent "RelayerAdded" [
    { name := "relayer", ty := ParamType.address, kind := EventParamKind.indexed }
  ] &&
  hasEvent "RelayerRemoved" [
    { name := "relayer", ty := ParamType.address, kind := EventParamKind.indexed }
  ] &&
  hasEvent "VerifierRouterUpdated" [
    { name := "previousRouter", ty := ParamType.address, kind := EventParamKind.indexed },
    { name := "newRouter", ty := ParamType.address, kind := EventParamKind.indexed }
  ]

example : unlinkPoolEventMetadataMatchesSource = true := by native_decide

def unlinkPoolTransferWithBalanceCheckMatchesSource : Bool :=
  let helperOk :=
    UnlinkPool.spec.functions.any (fun fn =>
      fn.name == "transferWithBalanceCheck" &&
        fn.params.map (fun param => param.ty) == [
          permitTransferFromParam,
          ParamType.address,
          ParamType.bytes,
          ParamType.uint256,
          ParamType.bytes32
        ] &&
        fn.returns == [])
  let depositCallsHelper :=
    UnlinkPool.spec.functions.any (fun fn =>
      fn.name == "deposit" &&
        !fn.isInternal &&
        stmtListHasInternalCall "transferWithBalanceCheck" fn.body)
  helperOk && depositCallsHelper

example : unlinkPoolTransferWithBalanceCheckMatchesSource = true := by native_decide

private def hasPoolFieldSlot (name : String) (expectedSlot : Nat) : Bool :=
  UnlinkPool.spec.fields.any (fun field => field.name == name && field.slot == some expectedSlot)

private def hasPoolPackedFieldSlot (name : String) (expectedSlot offset width : Nat) : Bool :=
  UnlinkPool.spec.fields.any (fun field =>
    field.name == name &&
      field.slot == some expectedSlot &&
      field.packedBits == some { offset := offset, width := width })

def unlinkPoolStorageNamespacesMatchSource : Bool :=
  hasPoolFieldSlot "state_merkleRoot"
    0xd7df6c02d48ad87762ead6689b0b308617a10b99ac21276cc6fd199681dcb000 &&
  hasPoolPackedFieldSlot "state_merkleTree_maxIndex"
    0xd7df6c02d48ad87762ead6689b0b308617a10b99ac21276cc6fd199681dcb001 0 40 &&
  hasPoolPackedFieldSlot "state_merkleTree_numberOfLeaves"
    0xd7df6c02d48ad87762ead6689b0b308617a10b99ac21276cc6fd199681dcb001 40 40 &&
  hasPoolFieldSlot "state_merkleTree_elements"
    0xd7df6c02d48ad87762ead6689b0b308617a10b99ac21276cc6fd199681dcb002 &&
  hasPoolFieldSlot "state_rootSeen"
    0xd7df6c02d48ad87762ead6689b0b308617a10b99ac21276cc6fd199681dcb003 &&
  hasPoolFieldSlot "state_nullifierHashes"
    0xd7df6c02d48ad87762ead6689b0b308617a10b99ac21276cc6fd199681dcb004 &&
  hasPoolFieldSlot "state_verifierRouter"
    0xd7df6c02d48ad87762ead6689b0b308617a10b99ac21276cc6fd199681dcb005 &&
  hasPoolFieldSlot "relayersSlot"
    0xd8b607728433c567965c4023813a35a19b26751353d5652c8798f8eea4b19b00

example : unlinkPoolStorageNamespacesMatchSource = true := by native_decide

def verifierRouterEventMetadataMatchesSource : Bool :=
  hasRouterEvent "CircuitRegistered" [
    { name := "circuitId", ty := ParamType.uint256, kind := EventParamKind.indexed },
    { name := "verifier", ty := ParamType.address, kind := EventParamKind.unindexed },
    { name := "inputCount", ty := ParamType.uint256, kind := EventParamKind.unindexed },
    { name := "outputCount", ty := ParamType.uint256, kind := EventParamKind.unindexed }
  ] &&
  hasRouterEvent "CircuitActiveSet" [
    { name := "circuitId", ty := ParamType.uint256, kind := EventParamKind.indexed },
    { name := "active", ty := ParamType.uint256, kind := EventParamKind.unindexed }
  ]

example : verifierRouterEventMetadataMatchesSource = true := by native_decide

def verifierRouterEntrypointsMatchSource : Bool :=
  hasRouterEntrypoint "setCircuit" &&
  hasRouterEntrypoint "pauseCircuit" &&
  hasRouterEntrypoint "getCircuit" &&
  hasRouterEntrypoint "verifierToCircuitId" &&
  hasRouterEntrypoint "renounceOwnership" &&
  hasRouterEntrypoint "owner" &&
  hasRouterEntrypoint "pendingOwner" &&
  hasRouterEntrypoint "transferOwnership" &&
  hasRouterEntrypoint "acceptOwnership"

example : verifierRouterEntrypointsMatchSource = true := by native_decide

def verifierRouterCircuitStorageUsesMappingStruct : Bool :=
  VerifierRouter.spec.fields.any (fun field =>
    field.name == "circuits" &&
      match field.ty with
      | FieldType.mappingStruct MappingKeyType.uint256 members =>
          members.any (fun member => member.name == "verifier" && member.wordOffset == 0) &&
          members.any (fun member => member.name == "inputCount" && member.wordOffset == 0) &&
          members.any (fun member => member.name == "outputCount" && member.wordOffset == 0) &&
          members.any (fun member => member.name == "active" && member.wordOffset == 0)
      | _ => false)

example : verifierRouterCircuitStorageUsesMappingStruct = true := by native_decide

def caseReady : Bool := true

end Benchmark.Cases.UnlinkXyz.Pool
