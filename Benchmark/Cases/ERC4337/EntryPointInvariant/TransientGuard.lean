import Contracts.Common

namespace Benchmark.Cases.ERC4337.EntryPointInvariant

open Verity hiding pure bind
open Verity.EVM.Uint256
open Contracts

/-!
# Transient reentrancy guard smoke (EIP-1153)

This is a standalone generic smoke for contracts that actually use an
OpenZeppelin-style transient-storage mutex. It is intentionally **not** part
of the EntryPoint v0.9 model: the Solidity `nonReentrant` modifier in that
source is an EOA-only guard
`tx.origin == msg.sender && msg.sender.code.length == 0`, not a transient
mutex.
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
