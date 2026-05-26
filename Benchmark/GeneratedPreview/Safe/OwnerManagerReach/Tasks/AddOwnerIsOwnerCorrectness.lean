import Benchmark.Cases.Safe.OwnerManagerReach.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Safe.OwnerManagerReach

open Verity
open Verity.EVM.Uint256

/--
Functional correctness of `addOwner`: the new address becomes an owner
and all other addresses' ownership status is unchanged.

`isOwner s addr` holds iff `next s addr ≠ zeroAddress ∧ addr ≠ SENTINEL`.

Proof strategy: use `addOwner_next_eq` to characterise the post-state
`next` function, then split into the two conjuncts of `addOwner_correctness`.
For the new owner: `next s' owner = next s SENTINEL ≠ 0`.
For others: `next s' k = next s k` when `k ≠ SENTINEL` and `k ≠ owner`.
-/
theorem addOwner_isOwnerCorrectness
    (owner : Address) (s : ContractState)
    (hNotZero : (owner != zeroAddress) = true)
    (hNotSentinel : (owner != SENTINEL) = true)
    (hFresh : (wordToAddress (s.storageMap 0 owner) == zeroAddress) = true)
    (hPreInv : ownerListInvariant s) :
    let s' := ((OwnerManager.addOwner owner).run s).snd
    addOwner_correctness s s' owner := by
  -- Grindset-first skeleton. See harness/PROOF_PATTERNS.md.
  -- Try `grind` with contract symbol hints; fall back to `simp` /
  -- `by_cases` if grind leaves goals. Use `grind?` for hints.
  grind [OwnerManager.addOwner, OwnerManager.owners, OwnerManager.ownerCount]

end Benchmark.Cases.Safe.OwnerManagerReach
