import Benchmark.Cases.Safe.OwnerManagerReach.Specs
import Benchmark.Grindset

namespace Benchmark.Cases.Safe.OwnerManagerReach

open Verity
open Verity.EVM.Uint256

/--
Combined `ownerListInvariant` preservation under `removeOwner`.

Properties like noSelfLoops and owner ≠ prevOwner are derived internally
from ownerListInvariant + uniquePredecessor, not required as hypotheses.
-/
theorem removeOwner_ownerListInvariant
    (prevOwner owner : Address) (s : ContractState)
    (hNotZero : (owner != zeroAddress) = true)
    (hNotSentinel : (owner != SENTINEL) = true)
    (hPrevLink : (wordToAddress (s.storageMap 0 prevOwner) == owner) = true)
    (hOwnerInList : next s owner ≠ zeroAddress)
    (hPreInv : ownerListInvariant s)
    (hUniquePred : uniquePredecessor s)
    (hPrevNZ : prevOwner ≠ zeroAddress)
    (hZeroInert : next s zeroAddress = zeroAddress) :
    let s' := ((OwnerManager.removeOwner prevOwner owner).run s).snd
    ownerListInvariant s' := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Safe.OwnerManagerReach
