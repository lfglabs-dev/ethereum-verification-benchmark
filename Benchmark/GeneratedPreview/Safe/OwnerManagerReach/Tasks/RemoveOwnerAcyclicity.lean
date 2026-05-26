import Benchmark.Cases.Safe.OwnerManagerReach.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Safe.OwnerManagerReach

open Verity
open Verity.EVM.Uint256

/--
removeOwner preserves acyclicity of the owner linked list.

Acyclicity is a tautology — it holds for any state. The proof
(acyclic_generic) shows that any duplicate-free chain from SENTINEL's
successor ending at key ≠ SENTINEL cannot contain SENTINEL, purely
by the structure of the definitions. No pre-state acyclicity hypothesis
is needed.
-/
theorem removeOwner_acyclicity
    (prevOwner owner : Address) (s : ContractState)
    (hNotZero : (owner != zeroAddress) = true)
    (hNotSentinel : (owner != SENTINEL) = true)
    (hPrevLink : (wordToAddress (s.storageMap 0 prevOwner) == owner) = true)
    (hOwnerInList : next s owner ≠ zeroAddress) :
    acyclic ((OwnerManager.removeOwner prevOwner owner).run s).snd := by
  -- Grindset-first skeleton. See harness/PROOF_PATTERNS.md.
  -- Try `grind` with contract symbol hints; fall back to `simp` /
  -- `by_cases` if grind leaves goals. Use `grind?` for hints.
  grind [OwnerManager.removeOwner, OwnerManager.owners, OwnerManager.ownerCount]

end Benchmark.Cases.Safe.OwnerManagerReach
