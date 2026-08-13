import Verity.Specs.Common
import Benchmark.Cases.AragonOSx.ExecuteAuthorization.Contract

namespace Benchmark.Cases.AragonOSx.ExecuteAuthorization

open Verity

/-- The exact fixed-DAO EXECUTE permission resolution used by modeled `execute`. -/
def executeAuthorized
    (s : ContractState)
    (specificConditionAllows genericCallerConditionAllows genericTargetConditionAllows : Bool) : Prop :=
  DAOAuthorization.isExecuteGranted s.sender specificConditionAllows
    genericCallerConditionAllows genericTargetConditionAllows s =
      ContractResult.success true s

/-- The exact fixed-DAO ROOT permission resolution used by direct mutation entrypoints. -/
def rootAuthorized
    (s : ContractState)
    (specificConditionAllows genericCallerConditionAllows genericTargetConditionAllows : Bool) : Prop :=
  DAOAuthorization.isRootGranted s.sender specificConditionAllows
    genericCallerConditionAllows genericTargetConditionAllows s =
      ContractResult.success true s

/-- The modeled `execute` call returned successfully. -/
def executeSucceeds
    (s s' : ContractState)
    (specificConditionAllows genericCallerConditionAllows genericTargetConditionAllows : Bool) : Prop :=
  (DAOAuthorization.execute specificConditionAllows genericCallerConditionAllows
    genericTargetConditionAllows).run s = ContractResult.success () s'

/-- The modeled function-body boundary was reached and retained the original caller. -/
def actionStartedByOriginalCaller (s s' : ContractState) : Prop :=
  s'.storage 4 = 1 ∧
  s'.storage 5 = addressToWord s.sender

/-- A successful `execute` entry was authorized and reached the action boundary. -/
def authorizedExecutionStarted
    (s s' : ContractState)
    (specificConditionAllows genericCallerConditionAllows genericTargetConditionAllows : Bool) : Prop :=
  executeAuthorized s specificConditionAllows genericCallerConditionAllows
    genericTargetConditionAllows ∧
  actionStartedByOriginalCaller s s'

/-- A present caller-specific condition that denies is terminal: wildcard entries are
not consulted. A reverting condition is represented by the same false outcome because
`PermissionManager._checkCondition` catches the revert and returns false. -/
def specificConditionDenialIsTerminal_spec
    (s : ContractState) (specificStatus : Uint256) : Prop :=
  DAOAuthorization.isExecuteGranted s.sender false true true
      { s with storageMap := fun sl key =>
          if sl == 0 && key == s.sender then specificStatus else s.storageMap sl key } =
    ContractResult.success false
      { s with storageMap := fun sl key =>
          if sl == 0 && key == s.sender then specificStatus else s.storageMap sl key }


/-- A successful direct EXECUTE grant was admitted by ROOT authorization. -/
def grantExecuteRequiresRoot_spec
    (s : ContractState) (rootSpecificAllows rootGenericCallerAllows rootGenericTargetAllows : Bool) : Prop :=
  rootAuthorized s rootSpecificAllows rootGenericCallerAllows rootGenericTargetAllows

/-- A successful direct conditional EXECUTE grant was admitted by ROOT authorization. -/
def grantExecuteWithConditionRequiresRoot_spec
    (s : ContractState) (rootSpecificAllows rootGenericCallerAllows rootGenericTargetAllows : Bool) : Prop :=
  rootAuthorized s rootSpecificAllows rootGenericCallerAllows rootGenericTargetAllows

/-- A successful direct EXECUTE revocation was admitted by ROOT authorization. -/
def revokeExecuteRequiresRoot_spec
    (s : ContractState) (rootSpecificAllows rootGenericCallerAllows rootGenericTargetAllows : Bool) : Prop :=
  rootAuthorized s rootSpecificAllows rootGenericCallerAllows rootGenericTargetAllows

/-- A successful direct ROOT grant was admitted by existing ROOT authorization. -/
def grantRootRequiresRoot_spec
    (s : ContractState) (rootSpecificAllows rootGenericCallerAllows rootGenericTargetAllows : Bool) : Prop :=
  rootAuthorized s rootSpecificAllows rootGenericCallerAllows rootGenericTargetAllows

/-- A successful direct conditional ROOT grant was admitted by existing ROOT authorization. -/
def grantRootWithConditionRequiresRoot_spec
    (s : ContractState) (rootSpecificAllows rootGenericCallerAllows rootGenericTargetAllows : Bool) : Prop :=
  rootAuthorized s rootSpecificAllows rootGenericCallerAllows rootGenericTargetAllows

/-- A successful direct ROOT revocation was admitted by existing ROOT authorization. -/
def revokeRootRequiresRoot_spec
    (s : ContractState) (rootSpecificAllows rootGenericCallerAllows rootGenericTargetAllows : Bool) : Prop :=
  rootAuthorized s rootSpecificAllows rootGenericCallerAllows rootGenericTargetAllows

/-- Under established ROOT authorization, a grant that uses ANY_ADDR as target must
revert for the restricted permission rather than at the authorization guard. -/
def wildcardTargetGrantReverts_spec
    (who : Address) (result : ContractResult Unit) (s : ContractState)
    (rootSpecificAllows rootGenericCallerAllows rootGenericTargetAllows : Bool) : Prop :=
  who ≠ ANY_ADDR →
    rootAuthorized s rootSpecificAllows rootGenericCallerAllows rootGenericTargetAllows →
      result = ContractResult.revert "PermissionsForAnyAddressDisallowed" s

/-- Under established ROOT authorization, a restricted-permission grant to ANY_ADDR as
caller must revert for the wildcard restriction. -/
def wildcardCallerGrantReverts_spec
    (result : ContractResult Unit) (s : ContractState)
    (rootSpecificAllows rootGenericCallerAllows rootGenericTargetAllows : Bool) : Prop :=
  rootAuthorized s rootSpecificAllows rootGenericCallerAllows rootGenericTargetAllows →
    result = ContractResult.revert "PermissionsForAnyAddressDisallowed" s

end Benchmark.Cases.AragonOSx.ExecuteAuthorization
