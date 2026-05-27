import Benchmark.Cases.Safe.OwnerManagerReach.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Safe.OwnerManagerReach

open Verity
open Verity.EVM.Uint256

/--
setupOwners establishes the combined `ownerListInvariant` (base case).

After setupOwners(owner1, owner2, owner3), the linked list is:
  SENTINEL → owner1 → owner2 → owner3 → SENTINEL

Both directions of the biconditional hold: every node with a non-zero
successor is reachable from SENTINEL (by explicit chains), and every
node reachable from SENTINEL has a non-zero successor (because only
SENTINEL, owner1, owner2, owner3 are reachable, and they all have
non-zero successors).
-/
theorem setupOwners_ownerListInvariant
    (owner1 owner2 owner3 : Address) (s : ContractState)
    (h1NZ : (owner1 != zeroAddress) = true)
    (h1NS : (owner1 != SENTINEL) = true)
    (h2NZ : (owner2 != zeroAddress) = true)
    (h2NS : (owner2 != SENTINEL) = true)
    (h3NZ : (owner3 != zeroAddress) = true)
    (h3NS : (owner3 != SENTINEL) = true)
    (h12 : (owner1 != owner2) = true)
    (h13 : (owner1 != owner3) = true)
    (h23 : (owner2 != owner3) = true)
    (hClean : ∀ addr : Address, s.storageMap 0 addr = 0) :
    let s' := ((OwnerManager.setupOwners owner1 owner2 owner3).run s).snd
    ownerListInvariant s' := by
  -- Grindset-first skeleton. See harness/PROOF_PATTERNS.md.
  -- Try `grind` with contract symbol hints; fall back to `simp` /
  -- `by_cases` if grind leaves goals. Use `grind?` for hints.
  grind [OwnerManager.setupOwners, OwnerManager.owners, OwnerManager.ownerCount]

end Benchmark.Cases.Safe.OwnerManagerReach
