import Benchmark.Cases.Safe.OwnerManagerReach.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Safe.OwnerManagerReach

open Verity
open Verity.EVM.Uint256

/--
Certora `inListReachable` invariant preservation under `swapOwner`.

swapOwner atomically replaces oldOwner with newOwner in-place:
  owners[newOwner] = owners[oldOwner]
  owners[prevOwner] = newOwner
  owners[oldOwner] = 0

Proof strategy: newOwner inherits oldOwner's successor. For any key with
a non-zero successor in the post-state, its pre-state chain through
oldOwner can be adapted by replacing oldOwner with newOwner:
[... → prevOwner → oldOwner → X → ...] becomes
[... → prevOwner → newOwner → X → ...].
-/
theorem swapOwner_inListReachable
    (prevOwner oldOwner newOwner : Address) (s : ContractState)
    (hNewNotZero : (newOwner != zeroAddress) = true)
    (hNewNotSentinel : (newOwner != SENTINEL) = true)
    (hNewFresh : (wordToAddress (s.storageMap 0 newOwner) == zeroAddress) = true)
    (hOldNotZero : (oldOwner != zeroAddress) = true)
    (hOldNotSentinel : (oldOwner != SENTINEL) = true)
    (hPrevLink : (wordToAddress (s.storageMap 0 prevOwner) == oldOwner) = true)
    -- Pre-state invariant (full ownerListInvariant, not just inListReachable)
    (hPreInvFull : ownerListInvariant s)
    -- Unique predecessor: each non-zero node has at most one non-zero predecessor.
    (hUniquePred : uniquePredecessor s)
    -- prevOwner is non-zero (a valid list node)
    (hPrevNZ : prevOwner ≠ zeroAddress)
    -- Zero address maps to itself
    (hZeroInert : next s zeroAddress = zeroAddress) :
    let s' := ((OwnerManager.swapOwner prevOwner oldOwner newOwner).run s).snd
    inListReachable s' := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Safe.OwnerManagerReach
