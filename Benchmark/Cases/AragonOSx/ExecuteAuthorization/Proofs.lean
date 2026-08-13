import Benchmark.Cases.AragonOSx.ExecuteAuthorization.Specs

namespace Benchmark.Cases.AragonOSx.ExecuteAuthorization

open Verity hiding pure bind
open Verity.EVM.Uint256

set_option maxHeartbeats 2400000

@[simp] private theorem executeSpecific_slot : DAOAuthorization.executeSpecific.slot = 0 := rfl
@[simp] private theorem executeGenericTarget_slot : DAOAuthorization.executeGenericTarget.slot = 1 := rfl
@[simp] private theorem rootSpecific_slot : DAOAuthorization.rootSpecific.slot = 2 := rfl
@[simp] private theorem rootGenericTarget_slot : DAOAuthorization.rootGenericTarget.slot = 3 := rfl
@[simp] private theorem executeBodyEntered_slot : DAOAuthorization.executeBodyEntered.slot = 4 := rfl
@[simp] private theorem actionActor_slot : DAOAuthorization.actionActor.slot = 5 := rfl

@[simp] private theorem verity_pure_apply {α : Type} (value : α) (s : ContractState) :
    Verity.pure value s = ContractResult.success value s := rfl

@[simp] private theorem uint_zero_ne_one : (0 : Uint256) ≠ 1 := by decide
@[simp] private theorem uint_zero_ne_two : (0 : Uint256) ≠ 2 := by decide
@[simp] private theorem uint_one_ne_zero : (1 : Uint256) ≠ 0 := by decide
@[simp] private theorem uint_one_ne_two : (1 : Uint256) ≠ 2 := by decide
@[simp] private theorem uint_two_ne_zero : (2 : Uint256) ≠ 0 := by decide
@[simp] private theorem uint_two_ne_one : (2 : Uint256) ≠ 1 := by decide
@[simp] private theorem address_256_ne_zero : (256 : Address) ≠ 0 := by decide
@[simp] private theorem address_256_ne_two : (256 : Address) ≠ 2 := by decide

private lemma resolveRoot_of_guarded_success
    (s s' : ContractState)
    (specificAllows genericCallerAllows genericTargetAllows : Bool)
    (rest : Contract Unit)
    (h : (Verity.bind
          (DAOAuthorization.isRootGranted s.sender specificAllows genericCallerAllows genericTargetAllows)
          (fun allowed => Verity.bind
            (Verity.require allowed "Unauthorized(ROOT_PERMISSION_ID)")
            (fun _ => rest))).run s = ContractResult.success () s') :
    rootAuthorized s specificAllows genericCallerAllows genericTargetAllows := by
  unfold rootAuthorized
  unfold DAOAuthorization.isRootGranted at h ⊢
  by_cases hSender : s.sender = ANY_ADDR <;>
  by_cases hs2 : s.storageMap 2 s.sender = 2 <;>
  by_cases hs0 : s.storageMap 2 s.sender = 0 <;>
  by_cases hg2 : s.storageMap 2 ANY_ADDR = 2 <;>
  by_cases hg0 : s.storageMap 2 ANY_ADDR = 0 <;>
  by_cases ht2 : s.storageMap 3 s.sender = 2 <;>
  by_cases ht0 : s.storageMap 3 s.sender = 0 <;>
  cases specificAllows <;> cases genericCallerAllows <;> cases genericTargetAllows <;>
    simp_all [ANY_ADDR, getMapping, Contract.run, Verity.bind, Bind.bind,
      Verity.require, Verity.pure, Pure.pure]

/-- Successful entry into `DAO.execute` implies authorized execution started. -/
theorem execute_success_implies_authorized
    (specificAllows genericCallerAllows genericTargetAllows : Bool)
    (s s' : ContractState)
    (h : executeSucceeds s s' specificAllows genericCallerAllows genericTargetAllows) :
    authorizedExecutionStarted s s' specificAllows genericCallerAllows genericTargetAllows := by
  unfold executeSucceeds at h
  unfold authorizedExecutionStarted
  unfold DAOAuthorization.execute at h
  have hAuth : executeAuthorized s specificAllows genericCallerAllows genericTargetAllows := by
    unfold executeAuthorized
    unfold DAOAuthorization.isExecuteGranted at h ⊢
    by_cases hSender : s.sender = ANY_ADDR <;>
    by_cases hs2 : s.storageMap 0 s.sender = 2 <;>
    by_cases hs0 : s.storageMap 0 s.sender = 0 <;>
    by_cases hg2 : s.storageMap 0 ANY_ADDR = 2 <;>
    by_cases hg0 : s.storageMap 0 ANY_ADDR = 0 <;>
    by_cases ht2 : s.storageMap 1 s.sender = 2 <;>
    by_cases ht0 : s.storageMap 1 s.sender = 0 <;>
    cases specificAllows <;> cases genericCallerAllows <;> cases genericTargetAllows <;>
      simp_all [ANY_ADDR, msgSender, getMapping, setStorage, Contract.run,
        Verity.bind, Bind.bind, Verity.require, Verity.pure, Pure.pure]
  constructor
  · exact hAuth
  · unfold actionStartedByOriginalCaller
    unfold executeAuthorized at hAuth
    simp only [Contract.run, msgSender, Verity.bind, Bind.bind] at h
    rw [hAuth] at h
    simp [msgSender, setStorage, Contract.run, Verity.bind, Bind.bind,
      Verity.require, Verity.pure, Pure.pure] at h
    subst s'
    constructor <;> simp

/-- A present denying condition terminates lookup before wildcard fallbacks. -/
theorem specific_condition_denial_is_terminal
    (s : ContractState) (specificStatus : Uint256)
    (hNonzero : specificStatus ≠ 0) (hNotAllow : specificStatus ≠ 2) :
    specificConditionDenialIsTerminal_spec s specificStatus := by
  unfold specificConditionDenialIsTerminal_spec DAOAuthorization.isExecuteGranted
  simp [getMapping, getStorage, Contract.run, Verity.bind, Bind.bind, Pure.pure,
    hNonzero, hNotAllow]


/-- Successful direct EXECUTE grants require ROOT authorization. -/
theorem grant_execute_requires_root
    (who : Address) (whereKind : Uint256)
    (specificAllows genericCallerAllows genericTargetAllows : Bool)
    (s s' : ContractState)
    (h : (DAOAuthorization.grantExecute who whereKind specificAllows genericCallerAllows genericTargetAllows).run s =
      ContractResult.success () s') :
    grantExecuteRequiresRoot_spec s specificAllows genericCallerAllows genericTargetAllows := by
  unfold grantExecuteRequiresRoot_spec
  unfold DAOAuthorization.grantExecute at h
  exact resolveRoot_of_guarded_success s s' specificAllows genericCallerAllows genericTargetAllows _ h

/-- Successful conditional EXECUTE grants require ROOT authorization. -/
theorem grant_execute_with_condition_requires_root
    (who condition : Address) (whereKind : Uint256)
    (conditionIsContract supportsInterface : Bool)
    (specificAllows genericCallerAllows genericTargetAllows : Bool)
    (s s' : ContractState)
    (h : (DAOAuthorization.grantExecuteWithCondition who condition whereKind
      conditionIsContract supportsInterface specificAllows genericCallerAllows genericTargetAllows).run s =
      ContractResult.success () s') :
    grantExecuteWithConditionRequiresRoot_spec s specificAllows genericCallerAllows genericTargetAllows := by
  unfold grantExecuteWithConditionRequiresRoot_spec
  unfold DAOAuthorization.grantExecuteWithCondition at h
  exact resolveRoot_of_guarded_success s s' specificAllows genericCallerAllows genericTargetAllows _ h

/-- Successful direct EXECUTE revocations require ROOT authorization. -/
theorem revoke_execute_requires_root
    (who : Address) (whereKind : Uint256)
    (specificAllows genericCallerAllows genericTargetAllows : Bool)
    (s s' : ContractState)
    (h : (DAOAuthorization.revokeExecute who whereKind specificAllows genericCallerAllows genericTargetAllows).run s =
      ContractResult.success () s') :
    revokeExecuteRequiresRoot_spec s specificAllows genericCallerAllows genericTargetAllows := by
  unfold revokeExecuteRequiresRoot_spec
  unfold DAOAuthorization.revokeExecute at h
  exact resolveRoot_of_guarded_success s s' specificAllows genericCallerAllows genericTargetAllows _ h

/-- Successful direct ROOT grants require existing ROOT authorization. -/
theorem grant_root_requires_root
    (who : Address) (whereKind : Uint256)
    (specificAllows genericCallerAllows genericTargetAllows : Bool)
    (s s' : ContractState)
    (h : (DAOAuthorization.grantRoot who whereKind specificAllows genericCallerAllows genericTargetAllows).run s =
      ContractResult.success () s') :
    grantRootRequiresRoot_spec s specificAllows genericCallerAllows genericTargetAllows := by
  unfold grantRootRequiresRoot_spec
  unfold DAOAuthorization.grantRoot at h
  exact resolveRoot_of_guarded_success s s' specificAllows genericCallerAllows genericTargetAllows _ h

/-- Successful direct conditional ROOT grants require existing ROOT authorization. -/
theorem grant_root_with_condition_requires_root
    (who condition : Address) (whereKind : Uint256)
    (conditionIsContract supportsInterface : Bool)
    (specificAllows genericCallerAllows genericTargetAllows : Bool)
    (s s' : ContractState)
    (h : (DAOAuthorization.grantRootWithCondition who condition whereKind
      conditionIsContract supportsInterface specificAllows genericCallerAllows genericTargetAllows).run s =
      ContractResult.success () s') :
    grantRootWithConditionRequiresRoot_spec s specificAllows genericCallerAllows genericTargetAllows := by
  unfold grantRootWithConditionRequiresRoot_spec
  unfold DAOAuthorization.grantRootWithCondition at h
  exact resolveRoot_of_guarded_success s s' specificAllows genericCallerAllows genericTargetAllows _ h

/-- Successful direct ROOT revocations require existing ROOT authorization. -/
theorem revoke_root_requires_root
    (who : Address) (whereKind : Uint256)
    (specificAllows genericCallerAllows genericTargetAllows : Bool)
    (s s' : ContractState)
    (h : (DAOAuthorization.revokeRoot who whereKind specificAllows genericCallerAllows genericTargetAllows).run s =
      ContractResult.success () s') :
    revokeRootRequiresRoot_spec s specificAllows genericCallerAllows genericTargetAllows := by
  unfold revokeRootRequiresRoot_spec
  unfold DAOAuthorization.revokeRoot at h
  exact resolveRoot_of_guarded_success s s' specificAllows genericCallerAllows genericTargetAllows _ h

/-- Direct EXECUTE grants reject the ANY_ADDR target. -/
theorem grant_execute_rejects_wildcard_target
    (who : Address) (specificAllows genericCallerAllows genericTargetAllows : Bool)
    (s : ContractState) :
    wildcardTargetGrantReverts_spec
      who ((DAOAuthorization.grantExecute who 1 specificAllows genericCallerAllows genericTargetAllows).run s) s
      specificAllows genericCallerAllows genericTargetAllows := by
  unfold wildcardTargetGrantReverts_spec
  intro _
  intro hRoot
  unfold rootAuthorized at hRoot
  unfold DAOAuthorization.grantExecute
  simp only [Contract.run, msgSender, Verity.bind, Bind.bind]
  rw [hRoot]
  simp [Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure]

/-- Direct EXECUTE grants reject the ANY_ADDR caller. -/
theorem grant_execute_rejects_wildcard_caller
    (specificAllows genericCallerAllows genericTargetAllows : Bool)
    (s : ContractState) :
    wildcardCallerGrantReverts_spec
      ((DAOAuthorization.grantExecute ANY_ADDR 0 specificAllows genericCallerAllows genericTargetAllows).run s) s
      specificAllows genericCallerAllows genericTargetAllows := by
  unfold wildcardCallerGrantReverts_spec
  intro hRoot
  unfold rootAuthorized at hRoot
  unfold DAOAuthorization.grantExecute
  simp only [Contract.run, msgSender, Verity.bind, Bind.bind]
  rw [hRoot]
  simp [Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure, ANY_ADDR]

/-- Direct ROOT grants reject the ANY_ADDR target. -/
theorem grant_root_rejects_wildcard_target
    (who : Address) (specificAllows genericCallerAllows genericTargetAllows : Bool)
    (s : ContractState) :
    wildcardTargetGrantReverts_spec
      who ((DAOAuthorization.grantRoot who 1 specificAllows genericCallerAllows genericTargetAllows).run s) s
      specificAllows genericCallerAllows genericTargetAllows := by
  unfold wildcardTargetGrantReverts_spec
  intro _
  intro hRoot
  unfold rootAuthorized at hRoot
  unfold DAOAuthorization.grantRoot
  simp only [Contract.run, msgSender, Verity.bind, Bind.bind]
  rw [hRoot]
  simp [Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure]

/-- Direct ROOT grants reject the ANY_ADDR caller. -/
theorem grant_root_rejects_wildcard_caller
    (specificAllows genericCallerAllows genericTargetAllows : Bool)
    (s : ContractState) :
    wildcardCallerGrantReverts_spec
      ((DAOAuthorization.grantRoot ANY_ADDR 0 specificAllows genericCallerAllows genericTargetAllows).run s) s
      specificAllows genericCallerAllows genericTargetAllows := by
  unfold wildcardCallerGrantReverts_spec
  intro hRoot
  unfold rootAuthorized at hRoot
  unfold DAOAuthorization.grantRoot
  simp only [Contract.run, msgSender, Verity.bind, Bind.bind]
  rw [hRoot]
  simp [Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure, ANY_ADDR]

/-- Conditional EXECUTE grants reject the ANY_ADDR target after ROOT authorization. -/
theorem grant_execute_condition_rejects_wildcard_target
    (who : Address) (specificAllows genericCallerAllows genericTargetAllows : Bool)
    (s : ContractState) :
    wildcardTargetGrantReverts_spec
      who ((DAOAuthorization.grantExecuteWithCondition who 256 1 true true
        specificAllows genericCallerAllows genericTargetAllows).run s) s
      specificAllows genericCallerAllows genericTargetAllows := by
  unfold wildcardTargetGrantReverts_spec
  intro hWho
  unfold ANY_ADDR at hWho
  intro hRoot
  unfold rootAuthorized at hRoot
  unfold DAOAuthorization.grantExecuteWithCondition
  simp only [Contract.run, msgSender, Verity.bind, Bind.bind]
  rw [hRoot]
  simp [Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure, ANY_ADDR, hWho]

/-- Conditional EXECUTE grants reject the ANY_ADDR caller after ROOT authorization. -/
theorem grant_execute_condition_rejects_wildcard_caller
    (specificAllows genericCallerAllows genericTargetAllows : Bool)
    (s : ContractState) :
    wildcardCallerGrantReverts_spec
      ((DAOAuthorization.grantExecuteWithCondition ANY_ADDR 256 0 true true
        specificAllows genericCallerAllows genericTargetAllows).run s) s
      specificAllows genericCallerAllows genericTargetAllows := by
  unfold wildcardCallerGrantReverts_spec
  intro hRoot
  unfold rootAuthorized at hRoot
  unfold DAOAuthorization.grantExecuteWithCondition
  simp only [Contract.run, msgSender, Verity.bind, Bind.bind]
  rw [hRoot]
  simp [Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure, ANY_ADDR]

/-- Conditional ROOT grants reject the ANY_ADDR target after ROOT authorization. -/
theorem grant_root_condition_rejects_wildcard_target
    (who : Address) (specificAllows genericCallerAllows genericTargetAllows : Bool)
    (s : ContractState) :
    wildcardTargetGrantReverts_spec
      who ((DAOAuthorization.grantRootWithCondition who 256 1 true true
        specificAllows genericCallerAllows genericTargetAllows).run s) s
      specificAllows genericCallerAllows genericTargetAllows := by
  unfold wildcardTargetGrantReverts_spec
  intro hWho
  unfold ANY_ADDR at hWho
  intro hRoot
  unfold rootAuthorized at hRoot
  unfold DAOAuthorization.grantRootWithCondition
  simp only [Contract.run, msgSender, Verity.bind, Bind.bind]
  rw [hRoot]
  simp [Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure, ANY_ADDR, hWho]

/-- Conditional ROOT grants reject the ANY_ADDR caller after ROOT authorization. -/
theorem grant_root_condition_rejects_wildcard_caller
    (specificAllows genericCallerAllows genericTargetAllows : Bool)
    (s : ContractState) :
    wildcardCallerGrantReverts_spec
      ((DAOAuthorization.grantRootWithCondition ANY_ADDR 256 0 true true
        specificAllows genericCallerAllows genericTargetAllows).run s) s
      specificAllows genericCallerAllows genericTargetAllows := by
  unfold wildcardCallerGrantReverts_spec
  intro hRoot
  unfold rootAuthorized at hRoot
  unfold DAOAuthorization.grantRootWithCondition
  simp only [Contract.run, msgSender, Verity.bind, Bind.bind]
  rw [hRoot]
  simp [Verity.require, Verity.bind, Bind.bind, Verity.pure, Pure.pure, ANY_ADDR]

end Benchmark.Cases.AragonOSx.ExecuteAuthorization
