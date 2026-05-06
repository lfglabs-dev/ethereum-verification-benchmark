import Benchmark.Cases.Alchemix.EarmarkConservation.Specs
import Benchmark.Cases.Alchemix.EarmarkConservation.Contract
import Benchmark.Cases.Alchemix.EarmarkConservation.Proofs

/-!
  Hypothesis-by-hypothesis audit of `Proofs.lean`.

  Background: an early reviewer flagged six hypotheses on the
  preservation theorems and asked whether each was a real modeling
  assumption or a scope cut. This file is the per-hypothesis ledger of
  the answer:

    H1  Q128 idealization                    irreducible (modeling level)
    H2  Synced-at-touched-id                 discharged compositionally
    H3  lastAccruedRedemptionWeight ≠ 0      model artifact (counterexample below)
    H4  cumulativeEarmarked ≤ totalDebt − amount   discharged via sister invariant
    H5  accounts_earmarked ≤ cumulativeEarmarked   discharged from invariant + non-overflow
    H6  Σ unearmarkedTimesRSR = totalDebt − cumulativeEarmarked
                                              scope cut (counterexample below)

  H1 is irreducible at this abstraction level — it absorbs floor-
  rounding ULP drift in Q128 fixed-point arithmetic into an exact-
  rational idealization. Any attempt to discharge it would change the
  invariant we are proving (a quantitative bounded-drift theorem,
  out of scope).

  The remaining five are addressed below. H2/H4/H5 are discharged as
  Lean theorems. H3 and H6 are model-level falsifiable from explicit
  counterexample states. -/

namespace Benchmark.Cases.Alchemix.EarmarkConservation

open Verity
open Verity.EVM.Uint256
open Verity.Core (FiniteSet)

/-! ## H2 — discharged as a theorem

  H2 was the synced-at-touched-id precondition on
  `_subDebt_preserves_invariant` and `_subEarmarkedDebt_preserves_invariant`:

      accounts_lastAccruedEarmarkWeight s tokenId = _earmarkWeight s ∧
      accounts_lastAccruedRedemptionWeight s tokenId = _redemptionWeight s

  In deployed Solidity every call site for those operations invokes
  `_sync(tokenId)` immediately before, so H2 is established by the
  preceding step rather than being a hidden global property. The
  theorem below captures this directly: after `_sync(tokenId)`, the
  account at tokenId is synced at the current globals.

  This is the property used by the composite call-site theorems
  (`_sync_then_subDebt_preserves_invariant` /
  `_sync_then_subEarmarkedDebt_preserves_invariant`) to discharge the
  H2 hypothesis on the local theorems. -/

theorem H2_synced_after_sync
    (tokenId : Uint256) (s : ContractState) :
    let s' := ((AlchemistV3._sync tokenId).run s).snd
    accounts_lastAccruedEarmarkWeight s' tokenId = _earmarkWeight s' ∧
    accounts_lastAccruedRedemptionWeight s' tokenId = _redemptionWeight s' := by
  intro s'
  refine ⟨?_, ?_⟩
  · show s'.storageMapUint 102 tokenId = s'.storage 2
    rcases _sync_slot_write tokenId s with ⟨_h0, _h1, h2, _h3, _h4, _h5⟩
    rw [h2]
    exact _sync_writes_lastEW tokenId s
  · show s'.storageMapUint 103 tokenId = s'.storage 3
    rcases _sync_slot_write tokenId s with ⟨_h0, _h1, _h2, h3, _h4, _h5⟩
    rw [h3]
    exact _sync_writes_lastRW tokenId s

/-! ## H4 — discharged as a theorem

  H4 was the precondition `cumulativeEarmarked s ≤ sub (totalDebt s)
  amount` on `_subDebt_preserves_invariant`. It splits cleanly into
  the contract's *sister invariant*

      cumulativeEarmarked ≤ totalDebt    (`cumulativeEarmarked_le_totalDebt_spec`)

  proven preserved by every operation in `Proofs.lean`
  (`_sync_preserves_cumLeTotalDebt`, ..., `_earmark_preserves_cumLeTotalDebt`),
  and the call-site precondition

      amount ≤ totalDebt − cumulativeEarmarked

  which is the live-unearmarked-debt check the caller already does
  (an honest call-site precondition, not a hidden global property).

  The theorem below combines the two pieces into the original H4 form.
  Used inside `_sync_then_subDebt_preserves_invariant_v2` to discharge
  H4 from the public preservation API. -/

theorem H4_from_sister_invariant
    (s : ContractState) (amount : Uint256)
    (hSister : cumulativeEarmarked_le_totalDebt_spec s)
    (hAmountLeLive : amount ≤ sub (totalDebt s) (cumulativeEarmarked s)) :
    cumulativeEarmarked s ≤ sub (totalDebt s) amount := by
  show (cumulativeEarmarked s).val ≤ (sub (totalDebt s) amount).val
  have hCumLeTd : (cumulativeEarmarked s).val ≤ (totalDebt s).val := hSister
  have hSubLive : (sub (totalDebt s) (cumulativeEarmarked s)).val =
      (totalDebt s).val - (cumulativeEarmarked s).val :=
    Verity.Core.Uint256.sub_eq_of_le hCumLeTd
  have hAmtLeLiveVal :
      amount.val ≤ (totalDebt s).val - (cumulativeEarmarked s).val := by
    have hThis : amount.val ≤ (sub (totalDebt s) (cumulativeEarmarked s)).val :=
      hAmountLeLive
    rw [hSubLive] at hThis
    exact hThis
  have hAmtLeTd : amount.val ≤ (totalDebt s).val := by omega
  have hSubAmtVal : (sub (totalDebt s) amount).val =
      (totalDebt s).val - amount.val :=
    Verity.Core.Uint256.sub_eq_of_le hAmtLeTd
  rw [hSubAmtVal]
  omega

/-! ## H5 — discharged as a theorem

  H5 was the per-account precondition `accounts_earmarked s accountId ≤
  cumulativeEarmarked s` on `_subEarmarkedDebt_preserves_invariant`. It
  is implied by the combination of:

    * the conservation invariant (`Σ proj = cumulativeEarmarked`),
    * H2 at `accountId` (so `accounts_earmarked s accountId =
      projectedEarmarked s accountId`), and
    * no-overflow on the projection sum (a generic property of the
      projection sum the protocol's debt cap ensures by design).

  Under those three, "single summand ≤ Nat sum" rules out the modular
  wrap that would otherwise let one summand exceed the modular sum.
  The theorem below captures the discharge. -/

theorem H5_from_invariant_and_no_overflow
    (s : ContractState) (ids : FiniteSet Uint256) (accountId : Uint256)
    (hMem : accountId ∈ ids.elements)
    (hSyncedAtAccountId :
      accounts_lastAccruedEarmarkWeight s accountId = _earmarkWeight s ∧
      accounts_lastAccruedRedemptionWeight s accountId = _redemptionWeight s)
    (hQ128MulOne : ∀ x : Uint256, mulQ128 x ONE_Q128 = x)
    (hInvariant : sumProjectedEarmarked s ids = cumulativeEarmarked s)
    (hSumNoOverflow :
      ids.elements.foldl (fun b x => b + (projectedEarmarked s x).val) 0 <
        Verity.Core.Uint256.modulus) :
    accounts_earmarked s accountId ≤ cumulativeEarmarked s :=
  accounts_earmarked_le_cumulative_of_invariant s ids accountId hMem
    hSyncedAtAccountId hQ128MulOne hInvariant hSumNoOverflow

/-! ## H6 — reformulated as projected debt conservation

  H6 is the bridging identity used inside `_earmark_preserves_invariant`:

      _earmark_active s = true →
        ids.sum (earmark_unearmarkedTimesRSR s) =
          sub (totalDebt s) (cumulativeEarmarked s)

  It is *not* a property of arbitrary `(s, ids)` pairs — it depends on
  the contract's debt-conservation sister invariant. Without modeling
  debt-mutation operations (`_addDebt`, `_resetDebt`, the constructor
  seed), we cannot prove it as a true preservation invariant.

  **Cheap fix.** We reformulate the original H6 as the natural sister
  of the main invariant: `sumProjectedDebt = totalDebt` (see
  `projectedDebt_conservation_spec` in Specs.lean). The lemma
  `H6_from_projectedDebt_conservation` (in Proofs.lean) proves the two
  are equivalent under the main invariant + the line-1306 sister
  invariant. So a caller of `_earmark_preserves_invariant` who has the
  cleaner sister gets the original H6 form for free.

  The reformulation does not change what is or isn't proven about
  Alchemix — both forms are still hypotheses. But the new form is
  honest: it sits next to the main invariant as its obvious sister,
  making it clear that the assumption is "debt also conserves" rather
  than a Q128-projected technicality.

  We retain the original counterexample below — `H6_not_a_tautology`
  shows the H6 form (and equivalently the projected-debt-conservation
  form) is genuinely a hypothesis, not a model tautology.

  Non-empty witness: `totalDebt = 100`, `cumulativeEarmarked = 0`,
  `_transmuterEarmarkAmount = 50` (so `_earmark_active = true`),
  weights all set to `ONE_Q128`, and the single tracked account has
  `debt = 1`, `earmarked = 0`. This is exactly the situation where
  the (unmodeled) debt-conservation sister invariant fails:
  `Σ accounts_debt = 1 ≠ 100 = totalDebt`.

  Per-account `earmark_unearmarkedTimesRSR` for id 1 evaluates to 1
  (userExposure = 1, both survival ratios are ONE_Q128). So the LHS
  sum is 1, while the RHS is `sub 100 0 = 100`. -/

def h6_cex_state : ContractState :=
  { Verity.defaultState with
    «storage» := fun n =>
      if n = 1 then (100 : Uint256)         -- totalDebt
      else if n = 2 then ONE_Q128            -- _earmarkWeight
      else if n = 3 then ONE_Q128            -- _redemptionWeight
      else if n = 5 then (50 : Uint256)      -- transmuter amount
      else (0 : Uint256)
    «storageMapUint» := fun n k =>
      if n = 100 ∧ k = (1 : Uint256) then (1 : Uint256)         -- debt
      else if n = 102 ∧ k = (1 : Uint256) then ONE_Q128         -- lastAccruedEW
      else if n = 103 ∧ k = (1 : Uint256) then ONE_Q128         -- lastAccruedRW
      else (0 : Uint256) }

def h6_cex_ids : FiniteSet Uint256 :=
  ⟨[(1 : Uint256)], by simp⟩

/-- The pre-state side of H6 fires (`_earmark_active = true`). -/
theorem H6_active :
    _earmark_active (totalDebt h6_cex_state)
      (cumulativeEarmarked h6_cex_state)
      (h6_cex_state.storage 5) = true := by
  native_decide

/-- The H6 conclusion fails on the counterexample. -/
theorem H6_falsified :
    h6_cex_ids.sum (earmark_unearmarkedTimesRSR h6_cex_state) ≠
      sub (totalDebt h6_cex_state) (cumulativeEarmarked h6_cex_state) := by
  native_decide

/-- Packaged: a concrete `(s, ids)` falsifying H6. -/
theorem H6_not_a_tautology :
    ∃ (s : ContractState) (ids : FiniteSet Uint256),
      _earmark_active (totalDebt s) (cumulativeEarmarked s) (s.storage 5) = true ∧
      ids.sum (earmark_unearmarkedTimesRSR s) ≠
        sub (totalDebt s) (cumulativeEarmarked s) :=
  ⟨h6_cex_state, h6_cex_ids, H6_active, H6_falsified⟩

/-- **H6 cheap fix**: a caller with the cleaner projected-debt-conservation
    sister invariant + the main earmark invariant + the line-1306 sister
    invariant gets the original H6 form by composition. The bridge is
    `H6_from_projectedDebt_conservation` in Proofs.lean. -/
theorem H6_from_sister_invariant
    (s : ContractState) (ids : FiniteSet Uint256)
    (hMain : sumProjectedEarmarked s ids = cumulativeEarmarked s)
    (hSister : projectedDebt_conservation_spec s ids)
    (hCumLeTd : cumulativeEarmarked_le_totalDebt_spec s) :
    ids.sum (earmark_unearmarkedTimesRSR s) =
      sub (totalDebt s) (cumulativeEarmarked s) :=
  H6_from_projectedDebt_conservation s ids hMain hSister hCumLeTd

/-! ## H3 — counterexample

  H3 is the precondition `∀ id ∈ ids, accounts_lastAccruedRedemptionWeight
  s id ≠ 0` carried by `redeem_preserves_invariant`. We show it cannot
  be dropped: a state satisfying the conservation invariant in pre, and
  violating H3, can have the conservation invariant break in post-state
  after `redeem(amount)`.

  Storage layout of the witness (as in the `Proofs.lean` H3 commentary):
    storage 0  (cumulativeEarmarked)         = 2
    storage 1  (totalDebt)                   = 3
    storage 2  (_earmarkWeight)              = ONE_Q128
    storage 3  (_redemptionWeight)           = 0   ← witness of ¬H3 globally
    storageMapUint 100 1 (debt)              = 3
    storageMapUint 101 1 (earmarked)         = 2
    storageMapUint 102 1 (lastAccruedEW)     = ONE_Q128
    storageMapUint 103 1 (lastAccruedRW)     = 0   ← H3 violated
    ids = {1}.

  The post-state (after `redeem(1)`) has cumulativeEarmarked = 1 but
  the per-account projection still computes to 2 because both the
  pre and post `_redemptionWeight` and `lastAccruedRedemptionWeight`
  are zero, so the redemption survival ratio collapses to ONE_Q128
  via the `lastRW = rW` branch — the projection ignores the redeem
  step entirely. -/

def h3_cex_state : ContractState :=
  { Verity.defaultState with
    «storage» := fun n =>
      if n = 0 then (2 : Uint256)
      else if n = 1 then (3 : Uint256)
      else if n = 2 then ONE_Q128
      else (0 : Uint256)
    «storageMapUint» := fun n k =>
      if n = 100 ∧ k = (1 : Uint256) then (3 : Uint256)
      else if n = 101 ∧ k = (1 : Uint256) then (2 : Uint256)
      else if n = 102 ∧ k = (1 : Uint256) then ONE_Q128
      else (0 : Uint256) }

def h3_cex_ids : FiniteSet Uint256 :=
  ⟨[(1 : Uint256)], by simp⟩

/-- The conservation invariant holds in the pre-state. -/
theorem H3_pre_invariant :
    sumProjectedEarmarked h3_cex_state h3_cex_ids =
      cumulativeEarmarked h3_cex_state := by
  native_decide

/-- H3 is violated in the pre-state: the lastAccruedRedemptionWeight
    snapshot at the active id is zero. -/
theorem H3_violated :
    accounts_lastAccruedRedemptionWeight h3_cex_state (1 : Uint256) = 0 := by
  native_decide

/-- The conservation invariant *fails* in the post-state after
    `redeem(1)` — even though the pre-state satisfied it. The
    failure is caused by the lastRW = 0 condition that H3 was
    designed to rule out. -/
theorem H3_post_invariant_fails :
    let s' := ((AlchemistV3.redeem 1).run h3_cex_state).snd
    sumProjectedEarmarked s' h3_cex_ids ≠ cumulativeEarmarked s' := by
  native_decide

/-- Packaged: a concrete state where the conservation invariant
    holds, H3 fails, and `redeem` breaks the invariant. This shows
    H3 cannot be dropped from `redeem_preserves_invariant`. -/
theorem H3_required_for_redeem :
    ∃ (s : ContractState) (ids : FiniteSet Uint256) (id : Uint256) (amount : Uint256),
      id ∈ ids.elements ∧
      accounts_lastAccruedRedemptionWeight s id = 0 ∧
      sumProjectedEarmarked s ids = cumulativeEarmarked s ∧
      let s' := ((AlchemistV3.redeem amount).run s).snd
      sumProjectedEarmarked s' ids ≠ cumulativeEarmarked s' := by
  refine ⟨h3_cex_state, h3_cex_ids, (1 : Uint256), (1 : Uint256), ?_, ?_, ?_, ?_⟩
  · -- 1 ∈ {1}.elements
    show (1 : Uint256) ∈ [(1 : Uint256)]
    simp
  · exact H3_violated
  · exact H3_pre_invariant
  · exact H3_post_invariant_fails

end Benchmark.Cases.Alchemix.EarmarkConservation
