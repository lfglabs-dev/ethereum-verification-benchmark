import Benchmark.Cases.Alchemix.EarmarkConservation.Specs

namespace Benchmark.Cases.Alchemix.EarmarkConservation

open Verity
open Verity.EVM.Uint256

/--
Preservation of the lazy-projected earmark conservation invariant under
`syncAccount(id)`.

`syncAccount` writes one account's projected values into storage and
advances its weight snapshots. The projected sum is unchanged because
syncing replaces the stored value with what the projection already
returned at the current global weights.

Hypotheses on the placeholder:

  * `hQ128MulOne` — Q128 idealization. Under floor-rounding,
    `mulQ128 x ONE_Q128 = x` exactly when `x.val < 2^128`. The
    conservation invariant is the design-level statement that holds
    under no-rounding-drift; surfacing the identity as a hypothesis
    is documented in `Contract.lean` and `Specs.lean`.
-/
theorem _sync_preserves_invariant
    (s : ContractState)
    (ids : Verity.Core.FiniteSet Uint256)
    (tokenId : Uint256)
    (hQ128MulOne : ∀ x : Uint256, mulQ128 x ONE_Q128 = x) :
    let s' := ((AlchemistV3._sync tokenId).run s).snd
    _sync_preserves_invariant_spec s s' ids := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Alchemix.EarmarkConservation
