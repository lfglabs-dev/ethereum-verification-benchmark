import Benchmark.Cases.Safe.OwnerManagerReach.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Safe.OwnerManagerReach

open Verity
open Verity.EVM.Uint256

/--
addOwner preserves acyclicity of the owner linked list.

After addOwner(owner), the list becomes:
  SENTINEL → owner → old_head → ... → SENTINEL

Acyclicity is a tautology — it holds for any state. The proof
(acyclic_generic) shows that any duplicate-free chain from SENTINEL's
successor ending at key ≠ SENTINEL cannot contain SENTINEL, purely
by the structure of the definitions. No pre-state hypotheses are needed
beyond the Solidity require guards.
-/
theorem addOwner_acyclicity
    (owner : Address) (s : ContractState)
    (hNotZero : (owner != zeroAddress) = true)
    (hNotSentinel : (owner != SENTINEL) = true)
    (hFresh : (wordToAddress (s.storageMap 0 owner) == zeroAddress) = true) :
    acyclic ((OwnerManager.addOwner owner).run s).snd := by
  -- Grindset-first skeleton. See harness/PROOF_PATTERNS.md.
  -- Try `grind` with contract symbol hints; fall back to `simp` /
  -- `by_cases` if grind leaves goals. Use `grind?` for hints.
  grind [OwnerManager.addOwner, OwnerManager.owners, OwnerManager.ownerCount]

end Benchmark.Cases.Safe.OwnerManagerReach
