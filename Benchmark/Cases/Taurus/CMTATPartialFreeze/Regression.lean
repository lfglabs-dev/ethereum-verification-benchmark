import Benchmark.Cases.Taurus.CMTATPartialFreeze.Proofs

/-! Kernel-evaluated semantic regressions, not Solidity/EVM executions. -/
namespace Benchmark.Cases.Taurus.CMTATPartialFreeze.Regression
open Benchmark.Cases.Taurus.CMTATPartialFreeze
set_option maxHeartbeats 2000000
set_option maxRecDepth 2000

def initial : State where
  balances := fun a => if a = 1 then word 100 else word 0
  frozenTokens := fun a => if a = 1 then word 40 else word 0
  allowances := fun a b => if a = 1 ∧ b = 3 then word 90 else word 0
  addressFrozen := fun _ => false
  paused := false
  deactivated := false
  erc20Enforcer := fun a => a = 3
  defaultAdmin := fun _ => false

def successState (r : Result) : State :=
  match r with
  | .ok t => t
  | .error _ => initial

/-- Finite decidable observations make every expected execution kernel-checkable. -/
def observe (r : Result) : Except Error (List Nat) :=
  match r with
  | .error e => .error e
  | .ok s => .ok [balanceOf s 1, balanceOf s 2, getFrozenTokens s 1,
      (s.allowances 1 3).val]

theorem transfer60_success :
    transfer initial 1 2 (word 60) = .ok (successState (transfer initial 1 2 (word 60))) := by rfl

theorem transfer60_values : observe (transfer initial 1 2 (word 60)) = .ok [40,60,40,90] := by rfl

theorem transfer61_rejected : transfer initial 1 2 (word 61) = .error .activeBalance := by rfl

theorem self60_success :
    transfer initial 1 1 (word 60) = .ok (successState (transfer initial 1 1 (word 60))) := by rfl

theorem self60_values : observe (transfer initial 1 1 (word 60)) = .ok [100,0,40,90] := by rfl

theorem zero_success :
    transfer initial 1 2 (word 0) = .ok (successState (transfer initial 1 2 (word 0))) := by rfl

theorem zero_values : observe (transfer initial 1 2 (word 0)) = .ok [100,0,40,90] := by rfl

theorem finite_success : transferFrom initial 3 1 2 (word 60) =
    .ok (successState (transferFrom initial 3 1 2 (word 60))) := by rfl

theorem finite_values : observe (transferFrom initial 3 1 2 (word 60)) = .ok [40,60,40,30] := by rfl

def infinite : State := { initial with allowances := fun a b => if a = 1 ∧ b = 3 then maxWord else word 0 }

theorem max_success : transferFrom infinite 3 1 2 (word 60) =
    .ok (successState (transferFrom infinite 3 1 2 (word 60))) := by rfl

theorem max_values : observe (transferFrom infinite 3 1 2 (word 60)) =
    .ok [40,60,40,modulus - 1] := by rfl

/-- Shows the finite allowance write really succeeds before the later endpoint rejection. -/
theorem zero_endpoint_spend_success : _spendAllowance initial 1 3 (word 60) =
    .ok (successState (_spendAllowance initial 1 3 (word 60))) := by rfl

theorem zero_endpoint_spent_values : observe (_spendAllowance initial 1 3 (word 60)) =
    .ok [100,0,40,30] := by rfl

theorem zero_endpoint_later_failure :
    _transfer (successState (_spendAllowance initial 1 3 (word 60))) 1 0 (word 60) =
      .error .invalidReceiver := by rfl

theorem zero_endpoint_rejected : transferFrom initial 3 1 0 (word 60) =
    .error .invalidReceiver := by rfl

theorem zero_endpoint_rollback : transact initial (.transferFrom 3 1 0 (word 60)) =
    (false, initial) := error_atomic_rollback initial _ .invalidReceiver zero_endpoint_rejected

def overFrozen : State := { initial with frozenTokens := fun a => if a = 1 then word 101 else word 0 }

theorem overFrozen_rejected : transfer overFrozen 1 2 (word 0) = .error .arithmeticUnderflow := by rfl

theorem overFrozen_rollback : transact overFrozen (.transfer 1 2 (word 0)) = (false, overFrozen) :=
  error_atomic_rollback overFrozen _ .arithmeticUnderflow overFrozen_rejected

/-- Concrete successful backing writers, separate from the ordinary trace alphabet. -/
theorem freeze_success : freezePartialTokens initial 3 1 (word 20) =
    .ok (successState (freezePartialTokens initial 3 1 (word 20))) := by rfl

theorem freeze_values : observe (freezePartialTokens initial 3 1 (word 20)) = .ok [100,0,60,90] := by rfl

theorem unfreeze_success : unfreezePartialTokens initial 3 1 (word 20) =
    .ok (successState (unfreezePartialTokens initial 3 1 (word 20))) := by rfl

theorem unfreeze_values : observe (unfreezePartialTokens initial 3 1 (word 20)) = .ok [100,0,20,90] := by rfl

theorem nonvacuous_senderProtected :
    senderProtected initial (successState (transfer initial 1 2 (word 60))) (.transfer 1 2 (word 60)) :=
  transfer_senderProtected initial _ 1 2 (word 60) transfer60_success

theorem mixed_trace : traceProtected initial
    [.transfer 1 2 (word 60), .transfer 1 2 (word 1), .transfer 1 1 (word 0),
     .transferFrom 3 1 2 (word 0)] := all_traces_protected initial _

theorem regression_bundle :
    observe (transfer initial 1 2 (word 60)) = .ok [40,60,40,90] ∧
    transfer initial 1 2 (word 61) = .error .activeBalance ∧
    observe (transfer initial 1 1 (word 60)) = .ok [100,0,40,90] ∧
    observe (transfer initial 1 2 (word 0)) = .ok [100,0,40,90] ∧
    observe (transferFrom initial 3 1 2 (word 60)) = .ok [40,60,40,30] ∧
    observe (transferFrom infinite 3 1 2 (word 60)) = .ok [40,60,40,modulus - 1] ∧
    observe (_spendAllowance initial 1 3 (word 60)) = .ok [100,0,40,30] ∧
    transferFrom initial 3 1 0 (word 60) = .error .invalidReceiver ∧
    transact initial (.transferFrom 3 1 0 (word 60)) = (false, initial) ∧
    transfer overFrozen 1 2 (word 0) = .error .arithmeticUnderflow ∧
    observe (freezePartialTokens initial 3 1 (word 20)) = .ok [100,0,60,90] ∧
    observe (unfreezePartialTokens initial 3 1 (word 20)) = .ok [100,0,20,90] :=
  ⟨transfer60_values, transfer61_rejected, self60_values, zero_values, finite_values,
    max_values, zero_endpoint_spent_values, zero_endpoint_rejected, zero_endpoint_rollback,
    overFrozen_rejected, freeze_values, unfreeze_values⟩

#print axioms regression_bundle
#print axioms nonvacuous_senderProtected
#print axioms mixed_trace

end Benchmark.Cases.Taurus.CMTATPartialFreeze.Regression
