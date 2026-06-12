import Benchmark.Cases.Safe.OwnerManagerReach.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Safe.OwnerManagerReach

open Verity
open Verity.EVM.Uint256

/--
Combined `ownerListInvariant` preservation under `addOwner`.

The ownerListInvariant merges `inListReachable` and `reachableInList`:
membership (non-zero successor) is equivalent to reachability from
SENTINEL. This is strictly stronger than proving inListReachable alone.

Proof strategy: prove both directions of the biconditional separately.
The forward direction (membership → reachability) follows from the
existing inListReachable proof. The reverse direction (reachability →
membership) requires showing that the new chain structure doesn't
introduce reachability to nodes with zero successors.

Acyclicity and freshness are derived from ownerListInvariant internally,
not required as separate hypotheses.
-/
theorem addOwner_ownerListInvariant
    (owner : Address) (s : ContractState)
    (hNotZero : (owner != zeroAddress) = true)
    (hNotSentinel : (owner != SENTINEL) = true)
    (hFresh : (wordToAddress (s.storageMap 0 owner) == zeroAddress) = true)
    (hPreInv : ownerListInvariant s) :
    let s' := ((OwnerManager.addOwner owner).run s).snd
    ownerListInvariant s' := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Safe.OwnerManagerReach
