import Benchmark.Cases.Alchemix.EarmarkConservation.Specs

namespace Benchmark.Cases.Alchemix.EarmarkConservation

open Verity
open Verity.EVM.Uint256

/--
Preservation of the lazy-projected earmark conservation invariant under
`subDebt(tokenId, amount)`.

The operation decrements `totalDebt` and clamps `cumulativeEarmarked`
down to the new `totalDebt` if necessary. Under the invariant pre-state
together with `cumulativeEarmarked ≤ totalDebt - amount` (the line-1306
clamp guard from the source), the clamp is a no-op and conservation is
preserved.

Hypotheses on the placeholder (all acceptable):

  * `hQ128MulOne` — Q128 idealization. Disclosed in `Contract.lean`.
  * `hSyncedAtTokenId` — pre-state weight snapshots match the global
    weights at `tokenId`. Source enforces this by calling `_sync(id)`
    at every site that calls `_subDebt(id, ...)` (lines 502, 522, 567,
    590, 869, 1052).
  * `hCumulativeLeTotalDebt` — the operational pre-condition that the
    line-1306 clamp is inactive. Justified by the conservation
    invariant + the clamp at source line 1306 itself: any reachable
    state satisfies `cumulativeEarmarked ≤ totalDebt`, and the
    operational guard for `_subDebt` enforces `amount ≤
    accountDebt[tokenId]` so `totalDebt - amount` does not
    underflow. (Provable as a corollary; left as an acceptable
    hypothesis here to keep the proof tractable.)
-/
theorem _subDebt_preserves_invariant
    (s : ContractState)
    (ids : Verity.Core.FiniteSet Uint256)
    (tokenId amount : Uint256)
    (hQ128MulOne : ∀ x : Uint256, mulQ128 x ONE_Q128 = x)
    (hSyncedAtTokenId :
      accounts_lastAccruedEarmarkWeight s tokenId = _earmarkWeight s ∧
      accounts_lastAccruedRedemptionWeight s tokenId = _redemptionWeight s)
    (hCumulativeLeTotalDebt :
      cumulativeEarmarked s ≤ sub (totalDebt s) amount) :
    let s' := ((AlchemistV3._subDebt tokenId amount).run s).snd
    _subDebt_preserves_invariant_spec s s' ids tokenId := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Alchemix.EarmarkConservation
