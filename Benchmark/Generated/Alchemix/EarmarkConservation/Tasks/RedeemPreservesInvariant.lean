import Benchmark.Cases.Alchemix.EarmarkConservation.Specs

namespace Benchmark.Cases.Alchemix.EarmarkConservation

open Verity
open Verity.EVM.Uint256

/--
Preservation of the lazy-projected earmark conservation invariant under
`redeem(amount)`.

`redeem` multiplies `_redemptionWeight` and `cumulativeEarmarked` by
`ratioApplied`. Per-account projections scale by the same `ratioApplied`
via the redemption survival ratio shift; this is derived in the
reference proof from `redeem_slot_write` and the projection formula
using atomic Q128 algebra. Sum-distributes via Q128 linearity.

Hypotheses on the placeholder (all acceptable: Q128 atomic algebra +
one pre-state operational invariant of the contract):

  * `hQ128MulOne`, `hQ128OneMul`, `hQ128MulAssoc`, `hQ128MulLinear`,
    `hQ128DivCommScale`, `hQ128DivSelf`, `hQ128MulCancelOne` — atomic
    Q128 algebra identities. Each is a short universally-quantified
    equation. Captures the Q128 idealization disclosed in
    `Contract.lean` simplifications.
  * `hLastRWNonZero` — pre-state operational invariant of the
    contract: every account in `ids` has a non-zero
    `lastAccruedRedemptionWeight`. True because every account is
    initialized via `_sync(id)` at mint time, which writes the
    current global `_redemptionWeight` (always ≠ 0 since the global
    weight is initialized to `ONE_Q128`).

These hypotheses are NOT restatements of the conclusion. They are
either pure Q128 algebraic identities (independent of the contract
state) or pre-state-only operational invariants. The per-id projection
scaling and the global cumulative scaling are DERIVED in the reference
proof, not assumed.
-/
theorem redeem_preserves_invariant
    (s : ContractState)
    (ids : Verity.Core.FiniteSet Uint256)
    (amount : Uint256)
    (hQ128MulOne : ∀ x : Uint256, mulQ128 x ONE_Q128 = x)
    (hQ128OneMul : ∀ x : Uint256, mulQ128 ONE_Q128 x = x)
    (hQ128MulAssoc : ∀ a b c : Uint256,
      mulQ128 (mulQ128 a b) c = mulQ128 a (mulQ128 b c))
    (hQ128MulLinear : ∀ x y r : Uint256,
      mulQ128 (add x y) r = add (mulQ128 x r) (mulQ128 y r))
    (hQ128DivCommScale : ∀ a b r : Uint256,
      b ≠ 0 → divQ128 (mulQ128 a r) b = mulQ128 (divQ128 a b) r)
    (hQ128DivSelf : ∀ x : Uint256, x ≠ 0 → divQ128 x x = ONE_Q128)
    (hQ128MulCancelOne : ∀ x r : Uint256, x ≠ 0 → mulQ128 x r = x → r = ONE_Q128)
    (hLastRWNonZero : ∀ id ∈ ids.elements,
      accounts_lastAccruedRedemptionWeight s id ≠ 0) :
    let s' := ((AlchemistV3.redeem amount).run s).snd
    redeem_preserves_invariant_spec s s' ids := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Alchemix.EarmarkConservation
