import Benchmark.Cases.Alchemix.EarmarkConservation.Specs

namespace Benchmark.Cases.Alchemix.EarmarkConservation

open Verity
open Verity.EVM.Uint256

/--
Preservation of the lazy-projected earmark conservation invariant under
`subEarmarkedDebt(amount, accountId)`.

The operation reduces both the stored `accounts_earmarked[accountId]`
and the global `cumulativeEarmarked` by the same `earmarkToRemove =
min(min(amount, debt), earmarked)`. Under the invariant pre-state
plus the synced-at-accountId precondition, both decrements coincide
and the per-id projection at `accountId` drops by `earmarkToRemove`
(synced shortcut), while projections at all other ids are unchanged.

Hypotheses on the placeholder (all acceptable):

  * `hQ128MulOne` — Q128 idealization (see other tasks). Disclosed in
    `Contract.lean`.
  * `hSyncedAtAccountId` — pre-state weight snapshots match the
    global weights at `accountId`. Source enforces this by calling
    `_sync(id)` at every site that calls `_subEarmarkedDebt(.., id)`
    (lines 567, 590, 869, 1052).
  * `hAccountEarmarkedLeCumulative` — operational pre-condition that
    the line-1015 min-clamp does not activate. Justified by the
    invariant + accountId ∈ ids: at a synced account the projection
    equals the stored earmarked, and any single summand is ≤ the
    sum, which equals `cumulativeEarmarked` by the invariant.
-/
theorem _subEarmarkedDebt_preserves_invariant
    (s : ContractState)
    (ids : Verity.Core.FiniteSet Uint256)
    (amountInDebtTokens accountId : Uint256)
    (hQ128MulOne : ∀ x : Uint256, mulQ128 x ONE_Q128 = x)
    (hSyncedAtAccountId :
      accounts_lastAccruedEarmarkWeight s accountId = _earmarkWeight s ∧
      accounts_lastAccruedRedemptionWeight s accountId = _redemptionWeight s)
    (hAccountEarmarkedLeCumulative :
      accounts_earmarked s accountId ≤ cumulativeEarmarked s) :
    let s' := ((AlchemistV3._subEarmarkedDebt amountInDebtTokens accountId).run s).snd
    _subEarmarkedDebt_preserves_invariant_spec s s' ids accountId := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Alchemix.EarmarkConservation
