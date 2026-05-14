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

private def eventParamEq (a b : EventParam) : Bool :=
  a.name == b.name && a.ty == b.ty && a.kind == b.kind

private def eventDefEq (name : String) (params : List EventParam) (eventDef : EventDef) : Bool :=
  eventDef.name == name &&
    eventDef.params.length == params.length &&
    (eventDef.params.zip params).all (fun (actual, expected) => eventParamEq actual expected)

private def hasEvent (name : String) (params : List EventParam) : Bool :=
  UnlinkPool.spec.events.any (eventDefEq name params)

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

def caseReady : Bool := true

end Benchmark.Cases.UnlinkXyz.Pool
