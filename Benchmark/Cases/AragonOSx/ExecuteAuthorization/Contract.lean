import Contracts.Common

namespace Benchmark.Cases.AragonOSx.ExecuteAuthorization

open Verity hiding pure bind
open Verity.EVM.Uint256

/-!
  Focused Verity model of Aragon OSx `DAO.execute` authorization and the
  inherited `PermissionManager` mutation entrypoints.

  Upstream: aragon/osx
  Commit: daf4fbb06b89ab0a05516bccb70b625a1a38303b
  Sources:
  - src/core/dao/DAO.sol
  - src/core/permission/PermissionManager.sol

  Simplifications:
  - The model fixes `_where` to the DAO for ordinary entries and separates the
    ROOT and EXECUTE permission-hash domains into dedicated storage mappings.
    This preserves the authorization lookup order without modeling keccak256.
  - Generic-caller (`who = ANY_ADDR`) and generic-target (`where = ANY_ADDR`)
    entries are represented separately. Public ROOT and EXECUTE grants reject
    either wildcard, matching the source restriction.
  - Condition-contract calls are an external boundary. Their result for the
    exact `(where, who, permissionId, msg.data)` context is supplied as a Bool.
    A present condition that returns false terminates lookup and does not fall
    through to a wildcard entry.
  - `execute` records that the authorization boundary was crossed and its actor.
    The action-count bound, action loop, external calls, values, failure map, gas
    checks, return data, events, and reentrancy bookkeeping are outside this theorem.
  - Direct `grant`, `grantWithCondition`, and `revoke` effects are modeled for
    ROOT and EXECUTE. Bulk permission-operation loops are excluded because they
    use the same ROOT authorization modifier but add iteration semantics.
-/

def UNSET_FLAG : Uint256 := 0
def ALLOW_FLAG : Uint256 := 2
def ANY_ADDR : Address := 1461501637330902918203684832716283019655932542975

verity_contract DAOAuthorization where
  storage
    executeSpecific : Address → Uint256 := slot 0
    executeGenericTarget : Address → Uint256 := slot 1
    rootSpecific : Address → Uint256 := slot 2
    rootGenericTarget : Address → Uint256 := slot 3
    executeBodyEntered : Uint256 := slot 4
    actionActor : Uint256 := slot 5

  /- `PermissionManager.isGranted` for EXECUTE_PERMISSION_ID. The three Bool
     inputs are the results of condition calls for the exact call context. -/
  function isExecuteGranted
      (who : Address,
       specificConditionAllows : Bool,
       genericCallerConditionAllows : Bool,
       genericTargetConditionAllows : Bool) : Bool := do
    let specific ← getMapping executeSpecific who
    if specific == 2 then
      return true
    else
      if specific != 0 then
        return specificConditionAllows
      else
        if who == 1461501637330902918203684832716283019655932542975 then
          let genericTarget ← getMapping executeGenericTarget who
          if genericTarget != 0 then
            return genericTargetConditionAllows
          else
            return false
        else
          let genericCaller ← getMapping executeSpecific 1461501637330902918203684832716283019655932542975
          if genericCaller == 2 then
            return true
          else
            if genericCaller != 0 then
              return genericCallerConditionAllows
            else
              let genericTarget ← getMapping executeGenericTarget who
              if genericTarget != 0 then
                return genericTargetConditionAllows
              else
                return false

  /- `PermissionManager.isGranted` for ROOT_PERMISSION_ID. -/
  function isRootGranted
      (who : Address,
       specificConditionAllows : Bool,
       genericCallerConditionAllows : Bool,
       genericTargetConditionAllows : Bool) : Bool := do
    let specific ← getMapping rootSpecific who
    if specific == 2 then
      return true
    else
      if specific != 0 then
        return specificConditionAllows
      else
        if who == 1461501637330902918203684832716283019655932542975 then
          let genericTarget ← getMapping rootGenericTarget who
          if genericTarget != 0 then
            return genericTargetConditionAllows
          else
            return false
        else
          let genericCaller ← getMapping rootSpecific 1461501637330902918203684832716283019655932542975
          if genericCaller == 2 then
            return true
          else
            if genericCaller != 0 then
              return genericCallerConditionAllows
            else
              let genericTarget ← getMapping rootGenericTarget who
              if genericTarget != 0 then
                return genericTargetConditionAllows
              else
                return false

  /- `DAO.execute`, through the `auth(EXECUTE_PERMISSION_ID)` boundary. -/
  function execute
      (specificConditionAllows : Bool,
       genericCallerConditionAllows : Bool,
       genericTargetConditionAllows : Bool) : Unit := do
    let caller ← msgSender
    let allowed ← isExecuteGranted caller specificConditionAllows
      genericCallerConditionAllows genericTargetConditionAllows
    require allowed "Unauthorized(EXECUTE_PERMISSION_ID)"
    setStorage executeBodyEntered 1
    setStorage actionActor (addressToWord caller)

  /- `PermissionManager.grant(..., EXECUTE_PERMISSION_ID)`. `whereKind` is 0
     for this DAO, 1 for ANY_ADDR, and any other value for another target.
     Other-target writes are outside this DAO-focused storage slice. -/
  function grantExecute
      (who : Address, whereKind : Uint256,
       rootSpecificAllows : Bool,
       rootGenericCallerAllows : Bool,
       rootGenericTargetAllows : Bool) : Unit := do
    let caller ← msgSender
    let rootAllowed ← isRootGranted caller rootSpecificAllows
      rootGenericCallerAllows rootGenericTargetAllows
    require rootAllowed "Unauthorized(ROOT_PERMISSION_ID)"
    require (whereKind != 1) "PermissionsForAnyAddressDisallowed"
    require (who != 1461501637330902918203684832716283019655932542975) "PermissionsForAnyAddressDisallowed"
    if whereKind == 0 then
      let current ← getMapping executeSpecific who
      if current == 0 then
        setMapping executeSpecific who 2
      else
        pure ()
    else
      pure ()

  /- `PermissionManager.grantWithCondition(..., EXECUTE_PERMISSION_ID)`.
     Condition deployment/interface checks are explicit external preconditions. -/
  function grantExecuteWithCondition
      (who : Address, condition : Address,
       whereKind : Uint256, conditionIsContract : Bool, supportsInterface : Bool,
       rootSpecificAllows : Bool,
       rootGenericCallerAllows : Bool,
       rootGenericTargetAllows : Bool) : Unit := do
    let caller ← msgSender
    let rootAllowed ← isRootGranted caller rootSpecificAllows
      rootGenericCallerAllows rootGenericTargetAllows
    require rootAllowed "Unauthorized(ROOT_PERMISSION_ID)"
    require (condition != 0) "ConditionNotAContract"
    require (condition != 2) "ConditionNotAContract"
    require conditionIsContract "ConditionNotAContract"
    require supportsInterface "ConditionInterfaceNotSupported"
    require ((whereKind == 1 && who == 1461501637330902918203684832716283019655932542975) == false)
      "AnyAddressDisallowedForWhoAndWhere"
    require (whereKind != 1) "PermissionsForAnyAddressDisallowed"
    require (who != 1461501637330902918203684832716283019655932542975) "PermissionsForAnyAddressDisallowed"
    if whereKind == 0 then
      let current ← getMapping executeSpecific who
      let conditionWord := addressToWord condition
      if current == 0 then
        setMapping executeSpecific who conditionWord
      else
        require (current == conditionWord) "PermissionAlreadyGrantedForDifferentCondition"
    else
      pure ()

  /- `PermissionManager.revoke(..., EXECUTE_PERMISSION_ID)`. -/
  function revokeExecute
      (who : Address, whereKind : Uint256,
       rootSpecificAllows : Bool,
       rootGenericCallerAllows : Bool,
       rootGenericTargetAllows : Bool) : Unit := do
    let caller ← msgSender
    let rootAllowed ← isRootGranted caller rootSpecificAllows
      rootGenericCallerAllows rootGenericTargetAllows
    require rootAllowed "Unauthorized(ROOT_PERMISSION_ID)"
    if whereKind == 0 then
      let current ← getMapping executeSpecific who
      if current != 0 then
        setMapping executeSpecific who 0
      else
        pure ()
    else
      if whereKind == 1 then
        setMapping executeGenericTarget who 0
      else
        pure ()

  /- `PermissionManager.grant(..., ROOT_PERMISSION_ID)`. -/
  function grantRoot
      (who : Address, whereKind : Uint256,
       rootSpecificAllows : Bool,
       rootGenericCallerAllows : Bool,
       rootGenericTargetAllows : Bool) : Unit := do
    let caller ← msgSender
    let rootAllowed ← isRootGranted caller rootSpecificAllows
      rootGenericCallerAllows rootGenericTargetAllows
    require rootAllowed "Unauthorized(ROOT_PERMISSION_ID)"
    require (whereKind != 1) "PermissionsForAnyAddressDisallowed"
    require (who != 1461501637330902918203684832716283019655932542975) "PermissionsForAnyAddressDisallowed"
    if whereKind == 0 then
      let current ← getMapping rootSpecific who
      if current == 0 then
        setMapping rootSpecific who 2
      else
        pure ()
    else
      pure ()

  /- `PermissionManager.grantWithCondition(..., ROOT_PERMISSION_ID)`. -/
  function grantRootWithCondition
      (who : Address, condition : Address,
       whereKind : Uint256, conditionIsContract : Bool, supportsInterface : Bool,
       rootSpecificAllows : Bool,
       rootGenericCallerAllows : Bool,
       rootGenericTargetAllows : Bool) : Unit := do
    let caller ← msgSender
    let rootAllowed ← isRootGranted caller rootSpecificAllows
      rootGenericCallerAllows rootGenericTargetAllows
    require rootAllowed "Unauthorized(ROOT_PERMISSION_ID)"
    require (condition != 0) "ConditionNotAContract"
    require (condition != 2) "ConditionNotAContract"
    require conditionIsContract "ConditionNotAContract"
    require supportsInterface "ConditionInterfaceNotSupported"
    require ((whereKind == 1 && who == 1461501637330902918203684832716283019655932542975) == false)
      "AnyAddressDisallowedForWhoAndWhere"
    require (whereKind != 1) "PermissionsForAnyAddressDisallowed"
    require (who != 1461501637330902918203684832716283019655932542975) "PermissionsForAnyAddressDisallowed"
    if whereKind == 0 then
      let current ← getMapping rootSpecific who
      let conditionWord := addressToWord condition
      if current == 0 then
        setMapping rootSpecific who conditionWord
      else
        require (current == conditionWord) "PermissionAlreadyGrantedForDifferentCondition"
    else
      pure ()

  /- `PermissionManager.revoke(..., ROOT_PERMISSION_ID)`. -/
  function revokeRoot
      (who : Address, whereKind : Uint256,
       rootSpecificAllows : Bool,
       rootGenericCallerAllows : Bool,
       rootGenericTargetAllows : Bool) : Unit := do
    let caller ← msgSender
    let rootAllowed ← isRootGranted caller rootSpecificAllows
      rootGenericCallerAllows rootGenericTargetAllows
    require rootAllowed "Unauthorized(ROOT_PERMISSION_ID)"
    if whereKind == 0 then
      let current ← getMapping rootSpecific who
      if current != 0 then
        setMapping rootSpecific who 0
      else
        pure ()
    else
      if whereKind == 1 then
        setMapping rootGenericTarget who 0
      else
        pure ()

end Benchmark.Cases.AragonOSx.ExecuteAuthorization
