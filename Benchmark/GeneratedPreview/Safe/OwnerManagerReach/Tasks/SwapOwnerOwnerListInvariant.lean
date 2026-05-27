import Benchmark.Cases.Safe.OwnerManagerReach.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Safe.OwnerManagerReach

open Verity
open Verity.EVM.Uint256

/--
Combined `ownerListInvariant` preservation under `swapOwner`.

Properties like noSelfLoops, freshInList, and oldOwner ≠ prevOwner are
derived internally from ownerListInvariant + uniquePredecessor, not
required as hypotheses.
-/
theorem swapOwner_ownerListInvariant
    (prevOwner oldOwner newOwner : Address) (s : ContractState)
    (hNewNotZero : (newOwner != zeroAddress) = true)
    (hNewNotSentinel : (newOwner != SENTINEL) = true)
    (hNewFresh : (wordToAddress (s.storageMap 0 newOwner) == zeroAddress) = true)
    (hOldNotZero : (oldOwner != zeroAddress) = true)
    (hOldNotSentinel : (oldOwner != SENTINEL) = true)
    (hPrevLink : (wordToAddress (s.storageMap 0 prevOwner) == oldOwner) = true)
    (hPreInv : ownerListInvariant s)
    (hUniquePred : uniquePredecessor s)
    (hPrevNZ : prevOwner ≠ zeroAddress)
    (hZeroInert : next s zeroAddress = zeroAddress) :
    let s' := ((OwnerManager.swapOwner prevOwner oldOwner newOwner).run s).snd
    ownerListInvariant s' := by
  -- Grindset-first skeleton. See harness/PROOF_PATTERNS.md.
  -- Try `grind` with contract symbol hints; fall back to `simp` /
  -- `by_cases` if grind leaves goals. Use `grind?` for hints.
  grind [OwnerManager.swapOwner, OwnerManager.owners, OwnerManager.ownerCount]

end Benchmark.Cases.Safe.OwnerManagerReach
