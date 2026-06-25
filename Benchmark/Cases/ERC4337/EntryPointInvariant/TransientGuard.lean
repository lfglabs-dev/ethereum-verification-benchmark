import Contracts.Common
import Verity.Core

namespace Benchmark.Cases.ERC4337.EntryPointInvariant

open Verity hiding pure bind
open Verity.EVM.Uint256
open Contracts

/-!
# Transient reentrancy guard smoke (EIP-1153)

The transient-storage guard primitive and locked-reverts theorem now live
upstream in `Verity.Core`. This file remains only as a benchmark smoke that
the upstream theorem is available at the pinned dependency.
-/

theorem nonReentrantTransient_locked_reverts_smoke
    (lockOffset : Uint256) (body : Contract α) (s : ContractState)
    (hLocked : s.transientStorage (lockOffset : Nat) ≠ 0) :
    (Verity.nonReentrantTransient lockOffset body).run s =
      ContractResult.revert "ReentrancyGuardTransient: reentrant call" s :=
  Verity.nonReentrantTransient_locked_reverts lockOffset body s hLocked

end Benchmark.Cases.ERC4337.EntryPointInvariant
