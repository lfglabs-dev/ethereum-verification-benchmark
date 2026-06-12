import Benchmark.Cases.Safe.OwnerManagerReach.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Safe.OwnerManagerReach

open Verity
open Verity.EVM.Uint256

/--
Functional correctness of `removeOwner`: the removed address is no longer
an owner and all other addresses' ownership status is unchanged.

`isOwner s addr` holds iff `next s addr ≠ zeroAddress ∧ addr ≠ SENTINEL`.

Proof strategy: use `removeOwner_storageMap` to characterise the post-state
`next` function, then show `next s' owner = zeroAddress` and for all
`k ≠ owner`, `next s' k ≠ 0 ↔ next s k ≠ 0` by case-splitting on
`k = prevOwner`.
-/
theorem removeOwner_isOwnerCorrectness
    (prevOwner owner : Address) (s : ContractState)
    (hNotZero : (owner != zeroAddress) = true)
    (hNotSentinel : (owner != SENTINEL) = true)
    (hPrevLink : (wordToAddress (s.storageMap 0 prevOwner) == owner) = true)
    (hOwnerInList : next s owner ≠ zeroAddress) :
    let s' := ((OwnerManager.removeOwner prevOwner owner).run s).snd
    removeOwner_correctness s s' owner := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Safe.OwnerManagerReach
