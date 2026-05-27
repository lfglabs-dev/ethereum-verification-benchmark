import Benchmark.Cases.Safe.OwnerManagerReach.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Safe.OwnerManagerReach

open Verity
open Verity.EVM.Uint256

/--
Functional correctness of `swapOwner`: the old owner is removed, the new
owner is added, and all other addresses' ownership status is unchanged.

`isOwner s addr` holds iff `next s addr ≠ zeroAddress ∧ addr ≠ SENTINEL`.

Proof strategy: use `swapOwner_storageMap` to characterise the post-state
`next` function, then show:
  1. `next s' oldOwner = zeroAddress` (old owner removed)
  2. `next s' newOwner = next s oldOwner ≠ 0` (new owner added)
  3. For all `k ≠ oldOwner, k ≠ newOwner`: `next s' k ≠ 0 ↔ next s k ≠ 0`
     by case-splitting on `k = prevOwner`.
-/
theorem swapOwner_isOwnerCorrectness
    (prevOwner oldOwner newOwner : Address) (s : ContractState)
    (hNewNotZero : (newOwner != zeroAddress) = true)
    (hNewNotSentinel : (newOwner != SENTINEL) = true)
    (hNewFresh : (wordToAddress (s.storageMap 0 newOwner) == zeroAddress) = true)
    (hOldNotZero : (oldOwner != zeroAddress) = true)
    (hOldNotSentinel : (oldOwner != SENTINEL) = true)
    (hPrevLink : (wordToAddress (s.storageMap 0 prevOwner) == oldOwner) = true)
    (hOldInList : next s oldOwner ≠ zeroAddress) :
    let s' := ((OwnerManager.swapOwner prevOwner oldOwner newOwner).run s).snd
    swapOwner_correctness s s' oldOwner newOwner := by
  -- Grindset-first skeleton. See harness/PROOF_PATTERNS.md.
  -- Try `grind` with contract symbol hints; fall back to `simp` /
  -- `by_cases` if grind leaves goals. Use `grind?` for hints.
  grind [OwnerManager.swapOwner, OwnerManager.owners, OwnerManager.ownerCount]

end Benchmark.Cases.Safe.OwnerManagerReach
