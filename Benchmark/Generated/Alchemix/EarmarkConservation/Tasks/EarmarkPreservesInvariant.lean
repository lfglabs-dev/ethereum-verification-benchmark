import Benchmark.Cases.Alchemix.EarmarkConservation.Specs

namespace Benchmark.Cases.Alchemix.EarmarkConservation

open Verity
open Verity.EVM.Uint256

/--
Preservation of the lazy-projected earmark conservation invariant under
`_earmark()`.

`_earmark` multiplies `_earmarkWeight` by `ratioApplied` and adds
`effectiveEarmarked = liveUnearmarked - mulQ128(liveUnearmarked,
ratioApplied)` to `cumulativeEarmarked`. Each account's
`projectedEarmarked` increases by `mulQ128(unearmarkedRemaining_pre,
1 − ratioApplied)`; this is derived in the reference proof from
`_earmark_slot_write` and the projection formula using atomic Q128
algebra. Σ delta_id = effectiveEarmarked follows from Q128 linearity
plus the parallel debt-conservation invariant
`Σ unearmarkedRemaining * RSR = totalDebt − cumulativeEarmarked`.

Hypotheses on the placeholder (all acceptable: Q128 atomic algebra +
two pre-state operational invariants of the contract):

  * `hQ128MulOne`, `hQ128OneMul`, `hQ128MulComm`, `hQ128MulAssoc`,
    `hQ128MulLinear`, `hQ128MulSubDistrib`, `hQ128MulOneSub`,
    `hQ128MulAppliedLe`, `hQ128DivCommScale`, `hQ128DivSelf`,
    `hQ128MulCancelOne` — atomic Q128 algebra identities, each a short
    universally-quantified equation. Captures the Q128 idealization
    disclosed in `Contract.lean` simplifications.
  * `hLastEWNonZero` — pre-state operational invariant: every
    `id ∈ ids` has a non-zero `lastAccruedEarmarkWeight`. True because
    every account is initialized via `_sync(id)` at mint time.
  * `hSumZ_eq_liveUnearmarked` — parallel-debt-conservation corollary:
    when active, `Σ_id mulQ128(unearmarkedRemaining_id,
    redemptionSurvivalRatio_id) = totalDebt − cumulativeEarmarked`.
    This is a real protocol invariant about debt conservation
    (`Σ stored.debt = totalDebt` is preserved by `_addDebt` / `_subDebt`),
    NOT the conservation conclusion restated. It bridges per-account
    pre-state quantities to the global `liveUnearmarked` and is
    documented at `earmark_unearmarkedTimesRSR` in the reference
    proof.

These hypotheses are NOT restatements of the conclusion. They are
either pure Q128 algebraic identities, pre-state-only operational
invariants of the contract, or a single bridging summation identity
(itself a corollary of the parallel debt-conservation invariant).
-/
theorem _earmark_preserves_invariant
    (s : ContractState)
    (ids : Verity.Core.FiniteSet Uint256)
    (hQ128MulOne : ∀ x : Uint256, mulQ128 x ONE_Q128 = x)
    (hQ128OneMul : ∀ x : Uint256, mulQ128 ONE_Q128 x = x)
    (hQ128MulComm : ∀ a b : Uint256, mulQ128 a b = mulQ128 b a)
    (hQ128MulAssoc : ∀ a b c : Uint256,
      mulQ128 (mulQ128 a b) c = mulQ128 a (mulQ128 b c))
    (hQ128MulLinear : ∀ x y r : Uint256,
      mulQ128 (add x y) r = add (mulQ128 x r) (mulQ128 y r))
    (hQ128MulSubDistrib : ∀ x y r : Uint256,
      mulQ128 (sub x y) r = sub (mulQ128 x r) (mulQ128 y r))
    (hQ128MulOneSub : ∀ a r : Uint256,
      sub a (mulQ128 a r) = mulQ128 a (sub ONE_Q128 r))
    (hQ128MulAppliedLe : ∀ y : Uint256,
      mulQ128 y
        (_earmark_ratioApplied (totalDebt s) (cumulativeEarmarked s) (s.storage 5))
        ≤ y)
    (hQ128DivCommScale : ∀ a b r : Uint256,
      b ≠ 0 → divQ128 (mulQ128 a r) b = mulQ128 (divQ128 a b) r)
    (hQ128DivSelf : ∀ x : Uint256, x ≠ 0 → divQ128 x x = ONE_Q128)
    (hQ128MulCancelOne : ∀ x r : Uint256, x ≠ 0 → mulQ128 x r = x → r = ONE_Q128)
    (hLastEWNonZero : ∀ id ∈ ids.elements,
      accounts_lastAccruedEarmarkWeight s id ≠ 0)
    (hSumZ_eq_liveUnearmarked :
      _earmark_active (totalDebt s) (cumulativeEarmarked s) (s.storage 5) = true →
      ids.sum (earmark_unearmarkedTimesRSR s) = sub (totalDebt s) (cumulativeEarmarked s)) :
    let s' := ((AlchemistV3._earmark).run s).snd
    _earmark_preserves_invariant_spec s s' ids := by
  -- Replace this placeholder with a complete Lean proof.
  exact ?_

end Benchmark.Cases.Alchemix.EarmarkConservation
