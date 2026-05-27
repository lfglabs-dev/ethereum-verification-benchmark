import Benchmark.Cases.Safe.OwnerManagerReach.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Safe.OwnerManagerReach

open Verity
open Verity.EVM.Uint256

/--
Certora `inListReachable` invariant preservation under `removeOwner`.

After removing `owner` by unlinking it from `prevOwner`, show that every
node with a non-zero successor in the post-state is still reachable from
SENTINEL.

Proof strategy: The removed owner's mapping becomes 0 so it no longer
triggers the invariant. prevOwner now points to owner's old successor,
so chains that went through owner can "skip" it: replace
[... → prevOwner → owner → X → ...] with [... → prevOwner → X → ...].
All other next pointers are unchanged.
-/
theorem removeOwner_inListReachable
    (prevOwner owner : Address) (s : ContractState)
    (hNotZero : (owner != zeroAddress) = true)
    (hNotSentinel : (owner != SENTINEL) = true)
    (hPrevLink : (wordToAddress (s.storageMap 0 prevOwner) == owner) = true)
    -- The removed owner must have a non-zero successor (i.e. be in the list).
    (hOwnerInList : next s owner ≠ zeroAddress)
    -- Pre-state invariant
    (hPreInv : inListReachable s)
    -- Unique predecessor: each non-zero node has at most one non-zero predecessor.
    (hUniquePred : uniquePredecessor s)
    -- prevOwner is non-zero (a valid list node)
    (hPrevNZ : prevOwner ≠ zeroAddress)
    -- Zero address maps to itself
    (hZeroInert : next s zeroAddress = zeroAddress) :
    let s' := ((OwnerManager.removeOwner prevOwner owner).run s).snd
    inListReachable s' := by
  -- Grindset-first skeleton. See harness/PROOF_PATTERNS.md.
  -- Try `grind` with contract symbol hints; fall back to `simp` /
  -- `by_cases` if grind leaves goals. Use `grind?` for hints.
  grind [OwnerManager.removeOwner, OwnerManager.owners, OwnerManager.ownerCount]

end Benchmark.Cases.Safe.OwnerManagerReach
