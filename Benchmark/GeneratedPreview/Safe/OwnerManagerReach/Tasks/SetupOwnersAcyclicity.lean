import Benchmark.Cases.Safe.OwnerManagerReach.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Safe.OwnerManagerReach

open Verity
open Verity.EVM.Uint256

/--
setupOwners establishes acyclicity of the owner linked list (base case).

The constructed list SENTINEL → o1 → o2 → o3 → SENTINEL has no internal
cycles because all three owners are distinct, non-zero, and non-sentinel.
SENTINEL appears only as the list head and the terminal pointer
(o3 → SENTINEL), never in the interior of any chain starting from
SENTINEL's successor.
-/
theorem setupOwners_acyclicity
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
    acyclic s' := by
  -- Grindset-first skeleton. See harness/PROOF_PATTERNS.md.
  -- Try `grind` with contract symbol hints; fall back to `simp` /
  -- `by_cases` if grind leaves goals. Use `grind?` for hints.
  grind [OwnerManager.setupOwners, OwnerManager.owners, OwnerManager.ownerCount]

end Benchmark.Cases.Safe.OwnerManagerReach
