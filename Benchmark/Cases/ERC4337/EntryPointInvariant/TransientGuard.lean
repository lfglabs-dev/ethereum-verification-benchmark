import Contracts.Common

namespace Benchmark.Cases.ERC4337.EntryPointInvariant

open Verity hiding pure bind
open Verity.EVM.Uint256
open Contracts

/-!
# Transient reentrancy guard (EIP-1153)

EntryPoint v0.9 uses `ReentrancyGuardTransient`: the lock lives in
transient storage, not regular storage, so it is cleared automatically at
the end of the transaction. This module ports `Verity.nonReentrant` to
the transient-storage primitive and proves the same `_locked_reverts`
lemma against it.

This swap closes one of the residual trust assumptions: the storage-slot
nonReentrant we used in `Frame.lean` and `Bytecode.lean` is no longer the
proof target — the actual transient-storage shape is.
-/

/-- Transient analogue of `Verity.nonReentrant`. The lock lives in
    transient storage, mirroring OpenZeppelin's
    `ReentrancyGuardTransient`. -/
def nonReentrantTransient (lockOffset : Uint256) (body : Contract α) : Contract α :=
  fun s =>
    if s.transientStorage (lockOffset : Nat) == 0 then
      let sLocked := { s with
        transientStorage := fun i =>
          if i == (lockOffset : Nat) then 1 else s.transientStorage i }
      match body sLocked with
      | ContractResult.success a s' =>
          ContractResult.success a
            { s' with
              transientStorage := fun i =>
                if i == (lockOffset : Nat) then 0 else s'.transientStorage i }
      | ContractResult.revert msg s' =>
          ContractResult.revert msg
            { s' with
              transientStorage := fun i =>
                if i == (lockOffset : Nat) then 0 else s'.transientStorage i }
    else
      ContractResult.revert "ReentrancyGuardTransient: reentrant call" s

/-- The corresponding `_locked_reverts` lemma. When the transient lock is
    already set, every re-entry into the guarded body reverts and the
    pre-call state is preserved. -/
@[simp] theorem nonReentrantTransient_locked_reverts
    (lockOffset : Uint256) (body : Contract α) (s : ContractState)
    (hLocked : s.transientStorage (lockOffset : Nat) ≠ 0) :
    (nonReentrantTransient lockOffset body).run s =
      ContractResult.revert "ReentrancyGuardTransient: reentrant call" s := by
  have hNe : (s.transientStorage (lockOffset : Nat) == 0) = false := by
    simp [hLocked]
  simp [Contract.run, nonReentrantTransient, hNe]

/-- Storage-roll-back corollary specific to transient locks. -/
theorem nonReentrantTransient_revert_preserves_state
    (lockOffset : Uint256) (body : Contract α) (s : ContractState)
    (hLocked : s.transientStorage (lockOffset : Nat) ≠ 0) :
    ((nonReentrantTransient lockOffset body).run s).snd = s := by
  rw [nonReentrantTransient_locked_reverts lockOffset body s hLocked]
  rfl

end Benchmark.Cases.ERC4337.EntryPointInvariant
