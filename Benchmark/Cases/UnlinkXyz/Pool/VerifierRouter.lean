/-
  Verity model of `VerifierRouter`.

  Upstream: unlink-xyz/monorepo@7617b3eebcf37ab42124fe570eb7e065cf8c8461
  Source:   protocol/contracts/src/VerifierRouter.sol

  The source storage shape is preserved with a struct-valued mapping:

    mapping(bytes32 => Circuit) private _circuits;

  The Verity model keeps the Solidity storage surface for the router:
  word-encoded circuit ids, `Uint16` shape fields, a packed active flag, and
  the named `Circuit` return type.
-/
import Contracts.Common

namespace Benchmark.Cases.UnlinkXyz.Pool

open Contracts
open Verity hiding pure bind
open Verity.EVM.Uint256

verity_contract VerifierRouter where
  types
    Uint16 : Uint256

  storage
    ownerSlot        : Address := slot 0
    pendingOwnerSlot : Address := slot 1
    circuits : MappingStruct(Uint256,[
      verifier @word 0 packed(0,160),
      inputCount @word 0 packed(160,16),
      outputCount @word 0 packed(176,16),
      active @word 0 packed(192,8)
    ]) := slot 2
    verifierToCircuitIdSlot : Address → Uint256 := slot 3

  struct Circuit where
    verifier : Address,
    inputCount : Uint16,
    outputCount : Uint16,
    active : Uint256

  errors
    error VerifierRouterInvalidCircuitId ()
    error VerifierRouterInvalidVerifier ()
    error VerifierRouterInvalidShape ()
    error VerifierRouterShapeImmutable ()
    error VerifierRouterDuplicateVerifier ()
    error VerifierRouterUnknownCircuit (Uint256)
    error VerifierRouterRenounceOwnershipDisabled ()
    error OwnableUnauthorizedAccount (Address)
    error CallerNotPendingOwner ()

  event_defs
    event CircuitRegistered(@indexed circuitId : Uint256, verifier : Address,
      inputCount : Uint16, outputCount : Uint16)
    event CircuitActiveSet(@indexed circuitId : Uint256, active : Uint256)

    event OwnershipTransferStarted(@indexed previousOwner : Address, @indexed newOwner : Address)
    event OwnershipTransferred(@indexed previousOwner : Address, @indexed newOwner : Address)

  constants
    FALSE_WORD : Uint256 := 0
    TRUE_WORD  : Uint256 := 1

  constructor () := do
    let sender ← msgSender
    setStorageAddr ownerSlot sender

  function view owner () : Address := do
    let current ← getStorageAddr ownerSlot
    return current

  function view pendingOwner () : Address := do
    let pending ← getStorageAddr pendingOwnerSlot
    return pending

  function transferOwnership (newOwner : Address) : Unit := do
    let sender ← msgSender
    let currentOwner ← getStorageAddr ownerSlot
    requireError (sender == currentOwner) OwnableUnauthorizedAccount(sender)
    setStorageAddr pendingOwnerSlot newOwner
    emit "OwnershipTransferStarted" [addressToWord currentOwner, addressToWord newOwner]

  function acceptOwnership () : Unit := do
    let sender ← msgSender
    let pending ← getStorageAddr pendingOwnerSlot
    requireError (sender == pending) CallerNotPendingOwner()
    let previousOwner ← getStorageAddr ownerSlot
    setStorageAddr ownerSlot pending
    setStorageAddr pendingOwnerSlot zeroAddress
    emit "OwnershipTransferred" [addressToWord previousOwner, addressToWord pending]

  function setCircuit
      (circuitId : Uint256, verifierAddr : Address, inputCount : Uint16,
       outputCount : Uint16)
      local_obligations [verifier_code_existence := assumed "extcodesize verifier checks must match the Solidity code-existence boundary."]
      : Unit := do
    let sender ← msgSender
    let currentOwner ← getStorageAddr ownerSlot
    requireError (sender == currentOwner) OwnableUnauthorizedAccount(sender)
    requireError (circuitId != 0) VerifierRouterInvalidCircuitId()
    requireError (verifierAddr != zeroAddress) VerifierRouterInvalidVerifier()
    let codeLen := extcodesize (addressToWord verifierAddr)
    requireError (codeLen != 0) VerifierRouterInvalidVerifier()
    requireError (inputCount != 0) VerifierRouterInvalidShape()
    requireError (outputCount != 0) VerifierRouterInvalidShape()

    let oldVerifier ← structMember "circuits" circuitId "verifier"
    let oldActive ← structMember "circuits" circuitId "active"
    if oldVerifier != zeroAddress then
      let oldInputCount ← structMember "circuits" circuitId "inputCount"
      let oldOutputCount ← structMember "circuits" circuitId "outputCount"
      requireError (oldInputCount == inputCount) VerifierRouterShapeImmutable()
      requireError (oldOutputCount == outputCount) VerifierRouterShapeImmutable()
    else
      pure ()

    let existingIdForVerifier ← getMapping verifierToCircuitIdSlot verifierAddr
    if existingIdForVerifier != FALSE_WORD then
      requireError (existingIdForVerifier == circuitId) VerifierRouterDuplicateVerifier()
    else
      pure ()

    if oldVerifier != zeroAddress then
      if oldVerifier != verifierAddr then
        setMapping verifierToCircuitIdSlot oldVerifier FALSE_WORD
      else
        pure ()
    else
      pure ()

    setMapping verifierToCircuitIdSlot verifierAddr circuitId
    setStructMember "circuits" circuitId "verifier" verifierAddr
    setStructMember "circuits" circuitId "inputCount" inputCount
    setStructMember "circuits" circuitId "outputCount" outputCount
    setStructMember "circuits" circuitId "active" TRUE_WORD
    emit "CircuitRegistered"
      [circuitId, addressToWord verifierAddr, inputCount, outputCount]
    if oldVerifier != zeroAddress then
      if oldActive == FALSE_WORD then
        emit "CircuitActiveSet" [circuitId, TRUE_WORD]
      else
        pure ()
    else
      pure ()

  function pauseCircuit (circuitId : Uint256) : Unit := do
    let sender ← msgSender
    let currentOwner ← getStorageAddr ownerSlot
    requireError (sender == currentOwner) OwnableUnauthorizedAccount(sender)
    let verifierAddr ← structMember "circuits" circuitId "verifier"
    requireError (verifierAddr != zeroAddress) VerifierRouterUnknownCircuit(circuitId)
    setStructMember "circuits" circuitId "active" FALSE_WORD
    emit "CircuitActiveSet" [circuitId, FALSE_WORD]

  function view getCircuit
      (circuitId : Uint256) : Tuple [Address, Uint16, Uint16, Uint256] := do
    let verifierAddr ← structMember "circuits" circuitId "verifier"
    let inputCount ← structMember "circuits" circuitId "inputCount"
    let outputCount ← structMember "circuits" circuitId "outputCount"
    let active ← structMember "circuits" circuitId "active"
    return (verifierAddr, inputCount, outputCount, active)

  function view verifierToCircuitId (verifierAddr : Address) : Uint256 := do
    let circuitId ← getMapping verifierToCircuitIdSlot verifierAddr
    return circuitId

  function renounceOwnership () : Unit := do
    let sender ← msgSender
    let currentOwner ← getStorageAddr ownerSlot
    requireError (sender == currentOwner) OwnableUnauthorizedAccount(sender)
    revert VerifierRouterRenounceOwnershipDisabled()

end Benchmark.Cases.UnlinkXyz.Pool
