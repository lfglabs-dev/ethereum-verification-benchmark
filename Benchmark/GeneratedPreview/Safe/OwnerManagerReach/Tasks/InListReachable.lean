import Benchmark.Cases.Safe.OwnerManagerReach.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Safe.OwnerManagerReach

open Verity
open Verity.EVM.Uint256

/--
Certora `inListReachable` invariant preservation under `addOwner`.

Given that in the pre-state every node with a non-zero successor is reachable
from SENTINEL, show that the same holds in the post-state after inserting
`owner` at the head of the linked list.

Proof strategy: SENTINEL is trivially reachable (reflexivity). The new owner
is reachable via [SENTINEL, owner]. For any other key with a non-zero successor,
its next pointer is unchanged, so we can lift its pre-state witness chain to
the post-state and prepend the new path SENTINEL → owner → old_head.
-/
theorem in_list_reachable
    (owner : Address) (s : ContractState)
    (hNotZero : (owner != zeroAddress) = true)
    (hNotSentinel : (owner != SENTINEL) = true)
    (hFresh : (wordToAddress (s.storageMap 0 owner) == zeroAddress) = true)
    (hPreReach : ∀ key : Address, next s key ≠ zeroAddress → reachable s SENTINEL key)
    -- Raw acyclicity: SENTINEL ∉ any chain from next s SENTINEL.
    -- Strictly stronger than `acyclic s` (no noDuplicates guard).
    (hAcyclic : ∀ key : Address, ∀ chain : List Address,
      chain.head? = some (next s SENTINEL) →
      chain.getLast? = some key →
      isChain s chain →
      SENTINEL ∉ chain)
    -- Raw freshness: owner ∉ any chain from next s SENTINEL.
    -- Strictly stronger than `freshInList s owner` (no noDuplicates guard).
    (hOwnerFresh : ∀ key : Address, ∀ chain : List Address,
      chain.head? = some (next s SENTINEL) →
      chain.getLast? = some key →
      isChain s chain →
      owner ∉ chain) :
    in_list_reachable_spec s ((OwnerManager.addOwner owner).run s).snd := by
  -- Grindset-first skeleton. See harness/PROOF_PATTERNS.md.
  -- Try `grind` with contract symbol hints; fall back to `simp` /
  -- `by_cases` if grind leaves goals. Use `grind?` for hints.
  unfold in_list_reachable_spec
  grind [OwnerManager.addOwner, OwnerManager.owners, OwnerManager.ownerCount]

end Benchmark.Cases.Safe.OwnerManagerReach
