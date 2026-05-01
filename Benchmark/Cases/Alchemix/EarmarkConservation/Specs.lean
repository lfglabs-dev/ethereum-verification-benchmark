import Verity.Specs.Common
import Benchmark.Cases.Alchemix.EarmarkConservation.Contract

namespace Benchmark.Cases.Alchemix.EarmarkConservation

open Verity
open Verity.EVM.Uint256

-- We use `FiniteSet` from `Verity.Core` without `open Verity.Core` to
-- avoid an ambiguity with `Verity.Uint256` vs `Verity.Core.Uint256`.
abbrev FiniteSet := Verity.Core.FiniteSet

/-
  Specifications for the Alchemix V3 earmark conservation property.

  The team's stated invariant (Ov3rkoalafied, 2026-04-24):
    "The sum of all accounts' earmarked debt equals cumulativeEarmarked
     at all times, across every operation"

  This file formalizes that statement as the *lazy-projected* invariant
  (see Contract.lean for why the literal "stored sum" version is false on
  the deployed code). The lazy-projected version is what the design
  guarantees and is the property whose violation would actually break
  the protocol's collateral accounting.

  Storage layout (from verity_contract AlchemistV3):
    slot 0   : cumulativeEarmarked
    slot 1   : totalDebt
    slot 2   : _earmarkWeight
    slot 3   : _redemptionWeight
    slot 4   : _survivalAccumulator
    slot 5   : _transmuterEarmarkAmount  (ghost: abstracts _earmark pre-amble)

    slot 100 : _accounts[id].debt
    slot 101 : _accounts[id].earmarked
    slot 102 : _accounts[id].lastAccruedEarmarkWeight
    slot 103 : _accounts[id].lastAccruedRedemptionWeight
    slot 104 : _accounts[id].lastSurvivalAccumulator
-/

/-! ## Storage accessors (article-readable surface) -/

/-- Models `AlchemistV3.cumulativeEarmarked` (slot 0). -/
def cumulativeEarmarked (s : ContractState) : Uint256 := s.storage 0

/-- Models `AlchemistV3.totalDebt` (slot 1). -/
def totalDebt (s : ContractState) : Uint256 := s.storage 1

/-- Models `AlchemistV3._earmarkWeight` (slot 2). -/
def _earmarkWeight (s : ContractState) : Uint256 := s.storage 2

/-- Models `AlchemistV3._redemptionWeight` (slot 3). -/
def _redemptionWeight (s : ContractState) : Uint256 := s.storage 3

/-- Models `AlchemistV3._survivalAccumulator` (slot 4). -/
def _survivalAccumulator (s : ContractState) : Uint256 := s.storage 4

/-- Models `AlchemistV3._accounts[id].debt`. -/
def accounts_debt (s : ContractState) (id : Uint256) : Uint256 :=
  s.storageMapUint 100 id

/-- Models `AlchemistV3._accounts[id].earmarked` (the *stored* value; can be
    stale relative to `cumulativeEarmarked` between syncs — see
    `_computeUnrealizedAccount` / `projectedEarmarked` for the lazy-projected
    current value). -/
def accounts_earmarked (s : ContractState) (id : Uint256) : Uint256 :=
  s.storageMapUint 101 id

/-- Models `AlchemistV3._accounts[id].lastAccruedEarmarkWeight`. -/
def accounts_lastAccruedEarmarkWeight (s : ContractState) (id : Uint256) : Uint256 :=
  s.storageMapUint 102 id

/-- Models `AlchemistV3._accounts[id].lastAccruedRedemptionWeight`. -/
def accounts_lastAccruedRedemptionWeight (s : ContractState) (id : Uint256) : Uint256 :=
  s.storageMapUint 103 id

/-! ## Lazy projection — `_computeUnrealizedAccount`

  The Solidity `_computeUnrealizedAccount(account, eW, rW, sA)`
  (AlchemistV3.sol:1478-1579) returns a triple
  `(newDebt, newEarmarked, redeemedDebt)`. For the conservation
  invariant we only need the second component (`newEarmarked`), but we
  keep the source name on the function that produces all three so the
  lineage is obvious. `projectedEarmarked` is the thin extractor used
  by the invariant.

  Both mirror the within-epoch / within-survival-window path of the
  Solidity function — the same path that `Contract.lean`'s `_sync`
  commits to storage. Conservation between the projection and the
  global is what `_sync` is designed to maintain.
-/

/-- Output of `_computeUnrealizedAccount` (Solidity returns a triple).
    For the invariant we only consume `newEarmarked`. -/
structure ComputeUnrealizedAccountResult where
  newDebt : Uint256
  newEarmarked : Uint256
  redeemedDebt : Uint256

/-- Models `_computeUnrealizedAccount(account, _earmarkWeight,
    _redemptionWeight, _survivalAccumulator)`
    (AlchemistV3.sol:1478-1579), within-epoch / within-survival-window
    telescoped path, idealized (no Q128 floor-rounding drift). -/
def _computeUnrealizedAccount (s : ContractState) (id : Uint256)
    : ComputeUnrealizedAccountResult :=
  let eW    := _earmarkWeight s
  let rW    := _redemptionWeight s
  let lastEW := accounts_lastAccruedEarmarkWeight s id
  let lastRW := accounts_lastAccruedRedemptionWeight s id
  let dbt    := accounts_debt s id
  let earm   := accounts_earmarked s id

  -- src: AlchemistV3.sol:1747-1763 — _earmarkSurvivalRatio(lastEW, eW)
  let unearmarkSurvivalQ := div (mul eW ONE_Q128) lastEW
  let unearmarkSurvivalRatio :=
    if lastEW = eW then ONE_Q128
    else if lastEW = 0 then ONE_Q128
    else unearmarkSurvivalQ

  -- src: AlchemistV3.sol:1768-1789 — _redemptionSurvivalRatio(lastRW, rW)
  let redemptionSurvivalQ := div (mul rW ONE_Q128) lastRW
  let redemptionSurvivalRatio :=
    if lastRW = rW then ONE_Q128
    else if lastRW = 0 then ONE_Q128
    else redemptionSurvivalQ

  -- src: AlchemistV3.sol:1489-1497 — userExposure, unearmarkedRemaining, earmarkRaw
  let userExposure := if dbt > earm then sub dbt earm else 0
  let unearmarkedRemaining := div (mul userExposure unearmarkSurvivalRatio) ONE_Q128
  let earmarkRaw := sub userExposure unearmarkedRemaining

  -- src: AlchemistV3.sol:1530+1577 — newEarmarked (telescoped same-epoch)
  let totalEarmarkedNow := add earm earmarkRaw
  let newEarmarked := div (mul totalEarmarkedNow redemptionSurvivalRatio) ONE_Q128

  -- src: AlchemistV3.sol:1573-1576 — redeemedTotal, newDebt
  let redeemedFromAccount := sub totalEarmarkedNow newEarmarked
  let newDebt := if dbt ≥ redeemedFromAccount then sub dbt redeemedFromAccount else 0

  { newDebt := newDebt
    newEarmarked := newEarmarked
    redeemedDebt := redeemedFromAccount }

/-- Lazy-projected earmarked debt for an account, used by the conservation
    invariant. Equals `_computeUnrealizedAccount(s, id).newEarmarked`. -/
def projectedEarmarked (s : ContractState) (id : Uint256) : Uint256 :=
  (_computeUnrealizedAccount s id).newEarmarked

/-! ## The lazy-projected sum -/

/-- Sum of `projectedEarmarked` over a finite set of active token IDs.

    Mirrors `Verity.Specs.Common.Sum.sumBalances` for the Uint256-keyed
    case. The local helper exists because `Verity.Specs.Common.Sum` only
    provides `sumBalances` for `FiniteAddressSet` (slot 0 of
    `s.knownAddresses`); there is no parallel `sumBalancesUint` keyed off
    `FiniteSet Uint256`. See proposed Verity issue. -/
def sumProjectedEarmarked (s : ContractState) (ids : FiniteSet Uint256) : Uint256 :=
  ids.sum (fun id => projectedEarmarked s id)

/-- Sum of stored `account.earmarked` values over `ids`. The team's
    "literal" reading of the invariant. Provably *not* equal to
    `cumulativeEarmarked` in general — it equals it only when every id
    in `ids` has been synced at the current global weights. See
    `synced_corollary_spec`. -/
def sumStoredEarmarked (s : ContractState) (ids : FiniteSet Uint256) : Uint256 :=
  ids.sum (fun id => accounts_earmarked s id)

/-! ## The conservation invariant -/

/-- **Lazy-projected earmark conservation** (the headline invariant).

    The sum, over all active accounts, of the lazily-projected earmarked
    debt equals the global `cumulativeEarmarked`. The projection uses
    `_computeUnrealizedAccount` against the current global weights, so it
    reflects each account's "current" earmarked even when its stored field
    is stale.

    This is what the team meant by "the sum of all accounts' earmarked debt
    equals cumulativeEarmarked at all times, across every operation":
    the lazily-corrected sum, which is what every downstream consumer
    (`_calculateUnrealizedDebt`, redemption math, collateral debit) actually
    uses. -/
def earmark_conservation_spec
    (s : ContractState) (ids : FiniteSet Uint256) : Prop :=
  sumProjectedEarmarked s ids = cumulativeEarmarked s

/-- **Synced corollary** — the human-readable form, used in the case-study
    article alongside the lazy-projected statement.

    If every active account has been re-synced at the current global
    weights (so its stored earmarked equals its projection), then the
    literal sum of stored values equals `cumulativeEarmarked`. Implied by
    `earmark_conservation_spec` together with the assumption of full sync. -/
def synced_corollary_spec
    (s : ContractState) (ids : FiniteSet Uint256) : Prop :=
  (∀ id ∈ ids.elements, accounts_earmarked s id = projectedEarmarked s id) →
  sumStoredEarmarked s ids = cumulativeEarmarked s

/-! ## Per-operation preservation specs

  The conservation invariant must hold "at all times, across every
  operation". The skill workflow proves this by per-operation preservation:
  each operation maps a state satisfying the invariant to a state still
  satisfying it.

  In-scope operations: `_earmark`, `_sync`, `redeem`, `_subEarmarkedDebt`,
  `_subDebt`. (`_computeUnrealizedAccount` is pure read-only — it cannot
  violate the invariant.)
-/

/-- Preservation under `_earmark()`. -/
def _earmark_preserves_invariant_spec
    (s s' : ContractState) (ids : FiniteSet Uint256) : Prop :=
  earmark_conservation_spec s ids → earmark_conservation_spec s' ids

/-- Preservation under `_sync(tokenId)`. -/
def _sync_preserves_invariant_spec
    (s s' : ContractState) (ids : FiniteSet Uint256) : Prop :=
  earmark_conservation_spec s ids → earmark_conservation_spec s' ids

/-- Preservation under `redeem(amount)`. -/
def redeem_preserves_invariant_spec
    (s s' : ContractState) (ids : FiniteSet Uint256) : Prop :=
  earmark_conservation_spec s ids → earmark_conservation_spec s' ids

/-- Preservation under `_subEarmarkedDebt(amountInDebtTokens, accountId)`.

    This requires `accountId ∈ ids` — the operation is invariant-preserving
    only when applied to an account that's actually being tracked. -/
def _subEarmarkedDebt_preserves_invariant_spec
    (s s' : ContractState) (ids : FiniteSet Uint256)
    (accountId : Uint256) : Prop :=
  accountId ∈ ids.elements →
  earmark_conservation_spec s ids → earmark_conservation_spec s' ids

/-- Preservation under `_subDebt(tokenId, amount)`. -/
def _subDebt_preserves_invariant_spec
    (s s' : ContractState) (ids : FiniteSet Uint256)
    (tokenId : Uint256) : Prop :=
  tokenId ∈ ids.elements →
  earmark_conservation_spec s ids → earmark_conservation_spec s' ids

/-! ## Sanity properties (lemmas that should hold trivially) -/

/-- `cumulativeEarmarked ≤ totalDebt` — enforced by the clamp at
    AlchemistV3.sol:1306. Useful as a side-lemma in conservation proofs. -/
def cumulativeEarmarked_le_totalDebt_spec (s : ContractState) : Prop :=
  cumulativeEarmarked s ≤ totalDebt s

/-! ## Pure helpers from the contract bodies

  These mirror the values that `redeem` / `_earmark` compute internally
  from the contract state. They are spec-level pure functions; the
  reference proof reads them off the contract body via the slot-write
  lemmas. Exposed at the spec surface so theorem hypotheses can name
  them without dragging in `Proofs.lean`.
-/

/-- `ratioApplied` chosen by `redeem(amount)`. -/
def redeem_ratioApplied (amount cumulativeEarmarked_ : Uint256) : Uint256 :=
  let amountClamped := ite (amount > cumulativeEarmarked_) cumulativeEarmarked_ amount
  let ratioWantedRaw :=
    div (mul (sub cumulativeEarmarked_ amountClamped) ONE_Q128) cumulativeEarmarked_
  ite (amountClamped == cumulativeEarmarked_) 0 ratioWantedRaw

/-- `active` flag for `redeem(amount)`. -/
def redeem_active (amount cumulativeEarmarked_ : Uint256) : Bool :=
  let amountClamped := ite (amount > cumulativeEarmarked_) cumulativeEarmarked_ amount
  cumulativeEarmarked_ != 0 && amountClamped != 0

/-- `ratioApplied` chosen by `_earmark()`. -/
def _earmark_ratioApplied
    (totalDebt_ cumulativeEarmarked_ amountIn : Uint256) : Uint256 :=
  let liveUnearmarked := sub totalDebt_ cumulativeEarmarked_
  let amount := ite (amountIn > liveUnearmarked) liveUnearmarked amountIn
  let ratioWantedRaw :=
    div (mul (sub liveUnearmarked amount) ONE_Q128) liveUnearmarked
  ite (amount == liveUnearmarked) 0 ratioWantedRaw

/-- `active` flag for `_earmark()`. -/
def _earmark_active
    (totalDebt_ cumulativeEarmarked_ amountIn : Uint256) : Bool :=
  let liveUnearmarked := sub totalDebt_ cumulativeEarmarked_
  let amount := ite (amountIn > liveUnearmarked) liveUnearmarked amountIn
  totalDebt_ != 0 && amount != 0 && liveUnearmarked != 0

/-- `effectiveEarmarked` from `_earmark()`. -/
def _earmark_effectiveEarmarked
    (totalDebt_ cumulativeEarmarked_ amountIn : Uint256) : Uint256 :=
  let liveUnearmarked := sub totalDebt_ cumulativeEarmarked_
  let ratioApplied := _earmark_ratioApplied totalDebt_ cumulativeEarmarked_ amountIn
  sub liveUnearmarked (mulQ128 liveUnearmarked ratioApplied)

/-- Per-id Q128-projected live unearmarked exposure weighted through the
    redemption-window survival. Appears in the parallel-debt-conservation
    bridging hypothesis for `_earmark_preserves_invariant`. -/
def earmark_unearmarkedTimesRSR (s : ContractState) (id : Uint256) : Uint256 :=
  let eW    := _earmarkWeight s
  let rW    := _redemptionWeight s
  let lastEW := accounts_lastAccruedEarmarkWeight s id
  let lastRW := accounts_lastAccruedRedemptionWeight s id
  let dbt    := accounts_debt s id
  let earm   := accounts_earmarked s id
  let unearmarkSurvivalRatio :=
    if lastEW = eW then ONE_Q128
    else if lastEW = 0 then ONE_Q128
    else divQ128 eW lastEW
  let redemptionSurvivalRatio :=
    if lastRW = rW then ONE_Q128
    else if lastRW = 0 then ONE_Q128
    else divQ128 rW lastRW
  let userExposure := if dbt > earm then sub dbt earm else 0
  let unearmarkedRemaining := mulQ128 userExposure unearmarkSurvivalRatio
  mulQ128 unearmarkedRemaining redemptionSurvivalRatio

/-! ## Projected debt (sister of projectedEarmarked) -/

/-- Per-id Q128-projected debt: the natural sister of `projectedEarmarked`.

    Algebraically (under Q128 idealization, `dbt ≥ earm`):
        projectedDebt(s, id) = mulQ128 (accounts_debt s id) USR-redeem(id)

    Operationally, every account's "current" debt equals what
    `_computeUnrealizedAccount` would commit if `_sync` were called on
    it now: `projectedEarmarked + earmark_unearmarkedTimesRSR`. The
    first summand is the lazily-projected earmarked debt, the second
    is the lazily-projected live unearmarked debt; together they
    reconstruct the projected total debt at the id. -/
def projectedDebt (s : ContractState) (id : Uint256) : Uint256 :=
  add (projectedEarmarked s id) (earmark_unearmarkedTimesRSR s id)

/-- Sum of `projectedDebt` over a finite set of active token IDs.

    The sister of `sumProjectedEarmarked`: where
    `sumProjectedEarmarked` aggregates the per-id projected
    *earmarked debt*, this aggregates the per-id projected *total
    debt*. -/
def sumProjectedDebt (s : ContractState) (ids : FiniteSet Uint256) : Uint256 :=
  ids.sum (fun id => projectedDebt s id)

/-- **Projected debt conservation** — the sister of
    `earmark_conservation_spec`.

    `Σ projectedDebt(s, id) = totalDebt s`: the lazily-projected sum of
    every active account's total debt equals the global `totalDebt`.

    This is the sister-invariant version of the H6 hypothesis used in
    `_earmark_preserves_invariant`. The deployed contract maintains the
    storage-level invariant `Σ accounts_debt(id) = totalDebt`; this is
    its Q128-projected form. -/
def projectedDebt_conservation_spec
    (s : ContractState) (ids : FiniteSet Uint256) : Prop :=
  sumProjectedDebt s ids = totalDebt s

end Benchmark.Cases.Alchemix.EarmarkConservation
