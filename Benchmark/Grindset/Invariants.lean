/-
  Benchmark.Grindset.Invariants

  Mission A1 (grindset/a1-invariant-tags): re-export and tag domain-level invariant lemmas and
  case-local spec helpers with `@[grind …]` so the `grind` tactic can use them during proof search.

  Complementary to sibling worker S1 (`grindset/s1-verity-grindset`), who tags core operational
  primitives. A1 focuses on:

    • Verity sum-preservation invariants   (Verity.Proofs.Stdlib.ListSum,
                                              Verity.Specs.Common.Sum)
    • Verity mapping store/load identities (Verity.Proofs.Stdlib.MappingAutomation)
    • Verity ceil/floor-div + wad + safe-op bounds
                                              (Verity.Proofs.Stdlib.Math)
    • A single Uint256 cancellation lemma  (Verity.Core.Uint256.sub_add_cancel)
    • Case-local predicate unfolding       (Benchmark.Cases.*.Specs)

  See Benchmark/Grindset/INVARIANTS_AUDIT.md for per-entry rationale and rejection notes.

  Constraints honoured:
    - No Verity library file (`.lake/packages/verity/**`) is modified.
    - No `Benchmark/Cases/**/Specs.lean` or `Proofs.lean` is modified.
    - Only `attribute [grind …] Name` re-exports are applied here.

  Orientation choices:
    - `[grind =]` for equality lemmas whose conclusion is used as a bidirectional rewrite (the
      safer default when the hypotheses lack matchable patterns or are non-propositional).
    - `[grind →]` reserved for implications whose antecedents contain genuinely matchable
      patterns distinct from the conclusion (`safeAdd_some`, `*_monotone_*` that ship with
      `≤` antecedents containing the same `mulDiv` terms as the conclusion, etc.).
    - Case-local `def`s get plain `[grind]` which registers them as δ-unfold candidates.
-/

import Verity.Core.Uint256
import Verity.Proofs.Stdlib.Math
import Verity.Proofs.Stdlib.ListSum
import Verity.Proofs.Stdlib.MappingAutomation
import Verity.Specs.Common
import Verity.Specs.Common.Sum

import Benchmark.Cases.Kleros.SortitionTrees.Specs
import Benchmark.Cases.Lido.VaulthubLocked.Specs
import Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.Specs
import Benchmark.Cases.Safe.OwnerManagerReach.Specs
import Benchmark.Cases.Zama.ERC7984ConfidentialToken.Specs

namespace Benchmark.Grindset.Invariants

/-! ## 1. Core Uint256 cancellations

Almost all of `Verity.Core.Uint256`'s algebraic lemmas are already `@[simp]`. Two are not but are
genuinely useful for proof automation: the wrap-safe `sub_add_cancel` and the forward-only
`add_right_cancel`. -/

attribute [grind =] Verity.Core.Uint256.sub_add_cancel
attribute [grind →] Verity.Core.Uint256.add_right_cancel


/-! ## 2. ListSum — point-update / transfer conservation

Core balance-conservation invariants. The `_eq` countOcc lemmas tag cleanly as `[grind =]`; the
conditional `_ne` variants (with an `a ≠ t` antecedent) are forward-only and tagged `[grind →]`.
The three `map_sum_*` preservation theorems can't be tagged with either `→` (antecedent patterns
aren't extractable) or `=` (the LHS of the concluding equality doesn't mention every bound
parameter like `delta`/`src`/`dst`, so grind can't instantiate them from an E-match). Callers
should pull them in manually (e.g. `grind [map_sum_point_update]`); NOT TAGGED here to avoid a
loud-but-useless global registration. -/

attribute [grind =]
  Verity.Proofs.Stdlib.ListSum.countOcc_cons_eq
  Verity.Proofs.Stdlib.ListSum.countOccU_cons_eq
-- Conditional (`a ≠ t → …`) equalities: forward-only per the audit.
attribute [grind →]
  Verity.Proofs.Stdlib.ListSum.countOcc_cons_ne
  Verity.Proofs.Stdlib.ListSum.countOccU_cons_ne


/-! ## 3. sumBalances preservation over FiniteAddressSet

Namespace is `Verity.Specs.Common` (the file lives under Sum.lean but opens no sub-namespace).

Only the two "pure rewrite" theorems (`sumBalances_insert_existing`, `sumBalances_zero_of_all_zero`)
tag cleanly as `[grind =]` — grind can E-match their LHS to the goal without unknown parameters.
The other three (`_insert_new`, `_update_existing`, `balancesFinite_preserved_deposit`) mention
fresh parameters (`amount`, `old_amount`, record-update on `knownAddresses`) that don't appear on
the pattern LHS, so grind refuses to register them. Callers invoke these manually. -/

attribute [grind =]
  Verity.Specs.Common.sumBalances_insert_existing
  Verity.Specs.Common.sumBalances_zero_of_all_zero


/-! ## 4. Mapping store/load identities (MappingAutomation)

These are the single highest-impact cluster: every benchmark obligation of the form "after
`setMappingX slot k v`, reading back at the same key equals `v`, and reading at a distinct key
preserves the original" reduces to these core four shapes per mapping family.

All tagged `[grind =]`:
  - the `_same` / `_runValue` lemmas are pure equations;
  - the `_diff` lemmas have an antecedent (`k1 ≠ k2`) whose pattern can't be extracted by grind →,
    but tagging `=` still lets grind rewrite the `getMapping …` term and side-check the ineq;
  - the `_preserves_*` lemmas have no propositional hypothesis at all, so `=` is the only
    orientation accepted.
-/

-- 4a. Address → Uint256 mappings
attribute [grind =]
  Verity.Proofs.Stdlib.MappingAutomation.getMapping_runValue
  Verity.Proofs.Stdlib.MappingAutomation.setMapping_getMapping_same
  Verity.Proofs.Stdlib.MappingAutomation.setMapping_getMapping_diff
  Verity.Proofs.Stdlib.MappingAutomation.setMapping_preserves_other_slot
  Verity.Proofs.Stdlib.MappingAutomation.setMapping_preserves_storageMapUint
  Verity.Proofs.Stdlib.MappingAutomation.setMapping_preserves_storageMap2

-- 4b. Uint256 → Uint256 mappings
attribute [grind =]
  Verity.Proofs.Stdlib.MappingAutomation.getMappingUint_runValue
  Verity.Proofs.Stdlib.MappingAutomation.setMappingUint_getMappingUint_same
  Verity.Proofs.Stdlib.MappingAutomation.setMappingUint_getMappingUint_diff
  Verity.Proofs.Stdlib.MappingAutomation.setMappingUint_preserves_storage
  Verity.Proofs.Stdlib.MappingAutomation.setMappingUint_preserves_storageAddr
  Verity.Proofs.Stdlib.MappingAutomation.setMappingUint_preserves_storageMap
  Verity.Proofs.Stdlib.MappingAutomation.setMappingUint_preserves_storageMap2
  Verity.Proofs.Stdlib.MappingAutomation.setMappingUint_preserves_sender
  Verity.Proofs.Stdlib.MappingAutomation.setMappingUint_preserves_thisAddress
  Verity.Proofs.Stdlib.MappingAutomation.setMappingUint_preserves_events

-- 4c. Address → Address → Uint256 (nested) mappings
attribute [grind =]
  Verity.Proofs.Stdlib.MappingAutomation.getMapping2_runValue
  Verity.Proofs.Stdlib.MappingAutomation.setMapping2_getMapping2_same
  Verity.Proofs.Stdlib.MappingAutomation.setMapping2_getMapping2_diff_key1
  Verity.Proofs.Stdlib.MappingAutomation.setMapping2_getMapping2_diff_key2
  Verity.Proofs.Stdlib.MappingAutomation.setMapping2_preserves_storage
  Verity.Proofs.Stdlib.MappingAutomation.setMapping2_preserves_storageAddr
  Verity.Proofs.Stdlib.MappingAutomation.setMapping2_preserves_storageMap
  Verity.Proofs.Stdlib.MappingAutomation.setMapping2_preserves_storageMapUint
  Verity.Proofs.Stdlib.MappingAutomation.setMapping2_preserves_events


/-! ## 5. Ceil / floor division + wad + safe ops

All of `Verity.Proofs.Stdlib.Math` except commutativity rewrites (which are E-match loop traps).

Groups:
  • `*_nat_eq`          — bridge Uint256 op to Nat op (equational, the fits-within side is
                          checked as a hypothesis but has no matchable pattern).
  • `*_zero_*`          — identities with no precondition (equational).
  • `*_one_{left,right}` / `wDivUp_by_wad` — gated identities (forward, the gate has patterns).
  • `*_monotone_*`, `*_antitone_*` — monotonicity (forward, antecedent shares `mulDiv` patterns
                                      with conclusion).
  • `*_mul_le / _mul_ge / _mul_lt_add` — sandwich bounds (mixed; those whose antecedents lack
                                          matchable patterns fall back to `=`).
  • `mulDivUp_eq_mulDivDown_*` — exactness disjunctions (forward).
  • `*_cancel_*`        — conditional cancellation (forward).
  • `*_pos`             — positivity entailment (forward).
  • `safe{Add,Sub,Mul,Div}_*` — Option-elimination and result bounds (mix of `=` for identities
                                 and `→` for bound-producing lemmas).
-/

-- 5a. Nat bridges (conditional on a `fits_within` hypothesis, forward-only per the audit).
attribute [grind →]
  Verity.Proofs.Stdlib.Math.mulDivDown_nat_eq
  Verity.Proofs.Stdlib.Math.mulDivUp_nat_eq
  Verity.Proofs.Stdlib.Math.wMulDown_nat_eq
  Verity.Proofs.Stdlib.Math.wDivUp_nat_eq

-- 5b. Unconditional zero identities
attribute [grind =]
  Verity.Proofs.Stdlib.Math.mulDivDown_zero_left
  Verity.Proofs.Stdlib.Math.mulDivDown_zero_right
  Verity.Proofs.Stdlib.Math.mulDivUp_zero_left
  Verity.Proofs.Stdlib.Math.mulDivUp_zero_right
  Verity.Proofs.Stdlib.Math.wMulDown_zero_left
  Verity.Proofs.Stdlib.Math.wMulDown_zero_right
  Verity.Proofs.Stdlib.Math.wDivUp_zero

-- 5c. Gated identity rewrites
attribute [grind →]
  Verity.Proofs.Stdlib.Math.wMulDown_one_left
  Verity.Proofs.Stdlib.Math.wMulDown_one_right
  Verity.Proofs.Stdlib.Math.wDivUp_by_wad

-- 5d. Monotonicity / antitonicity (mulDivDown variants: antecedents lack patterns AND the
--     conclusion is `≤` not `=`, so neither `→` nor `=` works. Use plain `[grind]`.)
attribute [grind]
  Verity.Proofs.Stdlib.Math.mulDivDown_monotone_left
  Verity.Proofs.Stdlib.Math.mulDivDown_monotone_right
attribute [grind →]
  Verity.Proofs.Stdlib.Math.mulDivUp_monotone_left
  Verity.Proofs.Stdlib.Math.mulDivUp_monotone_right
  Verity.Proofs.Stdlib.Math.wMulDown_monotone_left
  Verity.Proofs.Stdlib.Math.wMulDown_monotone_right
  Verity.Proofs.Stdlib.Math.wDivUp_monotone_left
  Verity.Proofs.Stdlib.Math.wDivUp_antitone_right
  Verity.Proofs.Stdlib.Math.mulDivDown_antitone_divisor
  Verity.Proofs.Stdlib.Math.mulDivUp_antitone_divisor

-- 5e. Sandwich bounds (mulDivDown variants: conclusions are `≤` / `<`, so use plain `[grind]`)
attribute [grind]
  Verity.Proofs.Stdlib.Math.mulDivDown_mul_le
  Verity.Proofs.Stdlib.Math.mulDivDown_mul_lt_add
attribute [grind →]
  Verity.Proofs.Stdlib.Math.mulDivUp_mul_ge
  Verity.Proofs.Stdlib.Math.mulDivUp_mul_lt_add
  Verity.Proofs.Stdlib.Math.wMulDown_mul_le
  Verity.Proofs.Stdlib.Math.wMulDown_mul_lt_add
  Verity.Proofs.Stdlib.Math.wDivUp_mul_ge
  Verity.Proofs.Stdlib.Math.wDivUp_mul_lt_add
  Verity.Proofs.Stdlib.Math.mulDivDown_le_mulDivUp
  Verity.Proofs.Stdlib.Math.mulDivUp_le_mulDivDown_add_one

-- 5f. Exactness disjunctions
attribute [grind →]
  Verity.Proofs.Stdlib.Math.mulDivUp_eq_mulDivDown_of_dvd
  Verity.Proofs.Stdlib.Math.mulDivUp_eq_mulDivDown_add_one_of_not_dvd
  Verity.Proofs.Stdlib.Math.mulDivUp_eq_mulDivDown_or_succ

-- 5g. Conditional cancellations
attribute [grind →]
  Verity.Proofs.Stdlib.Math.mulDivDown_cancel_left
  Verity.Proofs.Stdlib.Math.mulDivDown_cancel_right
  Verity.Proofs.Stdlib.Math.mulDivUp_cancel_left
  Verity.Proofs.Stdlib.Math.mulDivUp_cancel_right

-- 5h. Positivity
attribute [grind →]
  Verity.Proofs.Stdlib.Math.mulDivDown_pos
  Verity.Proofs.Stdlib.Math.mulDivUp_pos
  Verity.Proofs.Stdlib.Math.wMulDown_pos
  Verity.Proofs.Stdlib.Math.wDivUp_pos

-- 5i. safeAdd
attribute [grind →]
  Verity.Proofs.Stdlib.Math.safeAdd_some
  Verity.Proofs.Stdlib.Math.safeAdd_none
  Verity.Proofs.Stdlib.Math.safeAdd_zero_left
  Verity.Proofs.Stdlib.Math.safeAdd_zero_right
  Verity.Proofs.Stdlib.Math.safeAdd_result_bounded

-- 5j. safeSub (zero/self are no-hypothesis identities → `=`)
attribute [grind =]
  Verity.Proofs.Stdlib.Math.safeSub_zero
  Verity.Proofs.Stdlib.Math.safeSub_self
attribute [grind →]
  Verity.Proofs.Stdlib.Math.safeSub_some
  Verity.Proofs.Stdlib.Math.safeSub_none
  Verity.Proofs.Stdlib.Math.safeSub_result_le

-- 5k. safeMul (zero identities → `=`, rest → `→`)
attribute [grind =]
  Verity.Proofs.Stdlib.Math.safeMul_zero_left
  Verity.Proofs.Stdlib.Math.safeMul_zero_right
attribute [grind →]
  Verity.Proofs.Stdlib.Math.safeMul_some
  Verity.Proofs.Stdlib.Math.safeMul_none
  Verity.Proofs.Stdlib.Math.safeMul_one_left
  Verity.Proofs.Stdlib.Math.safeMul_one_right
  Verity.Proofs.Stdlib.Math.safeMul_result_bounded

-- 5l. safeDiv (none/by_one are no-hypothesis identities, some/zero_num/self lack antecedent
--     patterns → all to `=`)
attribute [grind =]
  Verity.Proofs.Stdlib.Math.safeDiv_some
  Verity.Proofs.Stdlib.Math.safeDiv_none
  Verity.Proofs.Stdlib.Math.safeDiv_zero_numerator
  Verity.Proofs.Stdlib.Math.safeDiv_by_one
  Verity.Proofs.Stdlib.Math.safeDiv_self
attribute [grind →]
  Verity.Proofs.Stdlib.Math.safeDiv_result_le_numerator


/-! ## 6. Case-local predicate / accessor unfolding

These are `def`s (not theorems) in the Specs.lean files of the 7 active cases. Tagging a `def`
with `@[grind]` registers it as an unfolding candidate for grind — it will δ-reduce the head
when it appears in the goal. This is essential so grind can see the underlying
`storage`/`storageMap`/… reads that the definitions abbreviate.

Rejected on purpose:
  • `reachable` / `acyclic` / `freshInList` (Safe.OwnerManagerReach) — existential / universal
    over chain lists; unfolding inside grind creates unbounded witness search.
  • `calculateBuyReserve`, `calculateSellReserve`, `spotPrices` (NexusMutual/RammPriceBand in
    Contract.lean) — multi-branch computation, unfolding thrashes on case splits.
  • Plain numeric constants — simp handles them better.
  • Main obligation predicates (`*_spec` at top level) — we prove these, we don't unfold them.
-/

-- Kleros / SortitionTrees
attribute [grind] Benchmark.Cases.Kleros.SortitionTrees.leaf_sum

-- PaladinVotes / StreamRecoveryClaimUsdc
attribute [grind]
  Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.computedClaimAmount
  Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc.computedWethClaimAmount

-- Lido / VaulthubLocked (defs live in the adjacent Contract module)
attribute [grind]
  Benchmark.Cases.Lido.VaulthubLocked.ceilDiv
  Benchmark.Cases.Lido.VaulthubLocked.getPooledEthBySharesRoundUp

-- Zama / ERC7984ConfidentialToken — storage accessors
attribute [grind]
  Benchmark.Cases.Zama.ERC7984ConfidentialToken.balanceOf
  Benchmark.Cases.Zama.ERC7984ConfidentialToken.supply
  Benchmark.Cases.Zama.ERC7984ConfidentialToken.operatorExpiry

-- Safe / OwnerManagerReach — linked-list reachability / invariant predicates
attribute [grind]
  Benchmark.Cases.Safe.OwnerManagerReach.next
  Benchmark.Cases.Safe.OwnerManagerReach.isChain
  Benchmark.Cases.Safe.OwnerManagerReach.inListReachable
  Benchmark.Cases.Safe.OwnerManagerReach.reachableInList
  Benchmark.Cases.Safe.OwnerManagerReach.ownerListInvariant
  Benchmark.Cases.Safe.OwnerManagerReach.noDuplicates
  Benchmark.Cases.Safe.OwnerManagerReach.uniquePredecessor
  Benchmark.Cases.Safe.OwnerManagerReach.noSelfLoops
  Benchmark.Cases.Safe.OwnerManagerReach.isOwner

end Benchmark.Grindset.Invariants
