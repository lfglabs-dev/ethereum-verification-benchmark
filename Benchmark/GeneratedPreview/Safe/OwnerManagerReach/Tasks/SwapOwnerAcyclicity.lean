import Benchmark.Cases.Safe.OwnerManagerReach.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Safe.OwnerManagerReach

open Verity
open Verity.EVM.Uint256

/--
swapOwner preserves acyclicity of the owner linked list.

Acyclicity is a tautology — it holds for any state. The proof
(acyclic_generic) shows that any duplicate-free chain from SENTINEL's
successor ending at key ≠ SENTINEL cannot contain SENTINEL, purely
by the structure of the definitions. No pre-state hypotheses are needed
beyond the Solidity require guards.
-/
theorem swapOwner_acyclicity
    (prevOwner oldOwner newOwner : Address) (s : ContractState)
    (hNewNotZero : (newOwner != zeroAddress) = true)
    (hNewNotSentinel : (newOwner != SENTINEL) = true)
    (hNewFresh : (wordToAddress (s.storageMap 0 newOwner) == zeroAddress) = true)
    (hOldNotZero : (oldOwner != zeroAddress) = true)
    (hOldNotSentinel : (oldOwner != SENTINEL) = true)
    (hPrevLink : (wordToAddress (s.storageMap 0 prevOwner) == oldOwner) = true) :
    acyclic ((OwnerManager.swapOwner prevOwner oldOwner newOwner).run s).snd := by
  -- Grindset-first skeleton. See harness/PROOF_PATTERNS.md.
  -- Try `grind` with contract symbol hints; fall back to `simp` /
  -- `by_cases` if grind leaves goals. Use `grind?` for hints.
  grind [OwnerManager.swapOwner, OwnerManager.owners, OwnerManager.ownerCount]

end Benchmark.Cases.Safe.OwnerManagerReach
