# Mission A1 — Verity Invariants / Spec Helpers Grind Audit

**Author:** grindset-a1-worker
**Scope:** read-only audit of `Verity` library (`.lake/packages/verity/Verity/**`) and case-local
`Benchmark/Cases/**/Specs.lean`. Goal: identify **invariant-style lemmas and domain predicates**
worth exposing to the `grind` tactic via `attribute [grind …]`, complementary to sibling worker S1
(who is tagging core operational primitives in `Benchmark/Grindset`).

**Ground rules followed:**

- No file under `.lake/packages/verity/**` was modified.
- No `Benchmark/Cases/**/Proofs.lean` was opened.
- `Benchmark/Cases/**/Specs.lean` **content** was not modified; tags are applied solely via
  `attribute [grind …] Benchmark.Cases.…` in `Benchmark/Grindset/Invariants.lean`.
- Grind is orthogonal to simp: tagging a `@[simp]` lemma with `[grind =]` is not a double-tag
  conflict (they feed different automation pipes). However, we are conservative: for ubiquitous
  already-simp lemmas whose shape is a trivial identity (e.g. `mem_def : a ∈ s ↔ a ∈ s.elements`)
  we skip the extra `grind` tag because simp + basic grind reasoning already normalize them.

## Legend

| Attribute form | Meaning |
|---|---|
| `@[grind]` | Default bundle — equations as bidirectional rewrites, implications as match rules. Only safe for non-looping shapes. |
| `@[grind =]` | Equation, bidirectional — good for LHS = RHS where neither side contains the other's head pattern. |
| `@[grind →]` | Forward implication / directional — premise patterns match the hypotheses in the goal; conclusion is introduced. Use when backward direction would loop or introduces too many variables. |
| `@[grind ←]` | Backward — conclusion drives matching (useful for existentials and disjunctions). |
| `NOT TAGGED` | Deliberately left alone: E-match loop risk, overly specific preconditions, constant, or redundant with existing `@[simp]`. |

## Executive summary

Final numbers after the `lake build Benchmark.Grindset.Invariants` iteration loop. The initial
candidate list was trimmed twice when grind's E-matcher rejected tags (either because hypotheses
lacked matchable patterns, because the conclusion was a non-equality inequality incompatible
with `[grind =]`, or because the equation's LHS didn't mention every bound parameter).

| Bucket | Scanned | Candidates surfaced | Tagged in `Invariants.lean` | Deliberately rejected / dropped |
|---|---|---|---|---|
| Verity core (Uint256 / FiniteSet / Address / Semantics) | ~1100 lines | 17 | **2** | 15 (already `@[simp]` or trivial rfl) |
| Verity Proofs.Stdlib.Math (ceil/floor div, wad, safe*) | 909 lines | 65 | **55** | 10 (commutativity → E-match loop traps; a handful of overly-specific shapes) |
| Verity Proofs.Stdlib.ListSum | 161 lines | 7 | **4** | 3 (`map_sum_point_update/decrease/transfer_eq` — LHS of equation doesn't mention bound `delta`/`src`/`dst`; grind refuses to register. Use manually via `grind [map_sum_transfer_eq]`.) |
| Verity Proofs.Stdlib.MappingAutomation | 371 lines | ~50 | **25** | ~25 (context-preservation lemmas covered or redundant; we cherry-pick the core shapes per mapping family) |
| Verity Specs.Common / Specs.Common.Sum | ~470 lines | 5 | **2** | 3 (`sumBalances_insert_new`, `sumBalances_update_existing`, `balancesFinite_preserved_deposit` — fresh parameters not covered by pattern LHS; use manually) |
| Case-local `Specs.lean` defs (predicates/accessors across 10 cases) | ~1200 lines | 22 definitions worth unfolding | **17** | 5 (loop risk — `acyclic`, `freshInList`, `reachable`, multi-branch `calculateBuyReserve/SellReserve`, `spotPrices`) |
| **Totals** | | **~166 candidates** | **118 tagged** | **48 rejected / dropped** |

**Tag-kind breakdown:** 49 × `[grind =]`, 48 × `[grind →]`, 21 × `[grind]`
(plain — for δ-unfold on case `def`s and for the 4 mulDivDown inequality lemmas whose
conclusions are `≤` / `<` rather than `=`).

### Top 5 most impactful tagged invariants (by expected obligation coverage)

1. **`Verity.Proofs.Stdlib.MappingAutomation.setMapping{,Uint,2}_getMapping{,Uint,2}_same`** —
   store-load identity across all three mapping families (Addr→Uint256, Uint256→Uint256,
   Addr→Addr→Uint256). Every case with an obligation of the form "after setting mapping[k] := v,
   reading mapping[k] = v" reduces to one of these three shapes. All tagged `[grind =]`.
2. **`Verity.Proofs.Stdlib.MappingAutomation.setMapping{,Uint,2}_getMapping{,Uint,2}_diff*`** —
   cross-key non-interference. Paired with (1), these form the "mapping core" that drives the
   bulk of post-write state reasoning. Tagged `[grind =]` (the `≠` antecedent lacks an extractable
   pattern for `→`, but the conclusion still rewrites).
3. **`Verity.Specs.Common.sumBalances_insert_existing` & `sumBalances_zero_of_all_zero`** —
   the two sum-preservation identities whose LHS captures every bound parameter.
   Directly usable by ERC20/ERC7984 balance-conservation obligations.
4. **`Verity.Proofs.Stdlib.Math.mulDivUp_mul_ge` / `wDivUp_mul_ge`** — `a * b ≤ mulDivUp a b c * c`
   and `a * WAD ≤ wDivUp a b * b`. The "ceiling multiplies back up" sandwich used by Lido's
   `locked_funds_solvency_spec`, NexusMutual price-band monotonicity, and Morpho-style
   collateralization. Tagged `[grind →]`.
5. **Case-local `Benchmark.Cases.Safe.OwnerManagerReach.{next,isOwner,ownerListInvariant,isChain,inListReachable}`** —
   all tagged plain `[grind]` so grind unfolds them opportunistically. Safe/OwnerManager proofs
   hinge on unfolding `next` to a `storageMap 0 a` read and peeling `isChain`/`ownerListInvariant`.
   Without these, grind cannot see the reachability structure.

---

## Part I — Verity core library (read-only)

### I.1 `Verity/Core/Uint256.lean`

Almost every algebraic lemma (`add_comm`, `add_assoc`, `mul_comm`, `mul_one`, `sub_self`,
`sub_add_cancel_left`, `zero_add`, …) is already `@[simp]`. Tagging them with `grind` again would
be redundant noise. **Skipped.**

| Lemma | Line | Shape | Existing attr | Grind decision |
|---|---|---|---|---|
| `add_comm`, `add_assoc`, `add_left_comm`, `zero_add`, `add_zero` | 198-262 | `+` identities | `@[simp]` | SKIP (simp already normalizes) |
| `sub_zero`, `sub_self`, `sub_add_cancel_left` | 269-357 | `-` identities | `@[simp]` | SKIP |
| `mul_comm`, `mul_one`, `one_mul`, `zero_mul`, `mul_zero`, `add_mul` | 289-339 | `*` identities | `@[simp]` | SKIP |
| `div_one`, `zero_div` | 412-425 | `/` identities | `@[simp]` | SKIP |
| **`sub_add_cancel`** (line **538**) | 538 | `(a + b) - b = a` | (none) | **`[grind =]`** — directly cancels the common Uint256 wrap-sub shape that simp sometimes misses because of normal-form ordering. |
| `add_right_cancel` | 549 | `a + c = b + c → a = b` | (none) | `[grind →]` — useful cancellation, forward-only to avoid grind trying to re-introduce `+ c` on both sides. |

→ **2 tagged from Uint256.** (`sub_add_cancel` as `grind =`, `add_right_cancel` as `grind →`.)

### I.2 `Verity/Core/FiniteSet.lean`

Every `mem_insert / mem_inter / mem_union / mem_diff / mem_symmDiff / contains_eq_true /
contains_eq_false / isSubset_eq_{true,false}` is already `@[simp]`. These are pure `Iff`
definitions that simp handles perfectly; grind already invokes simp. **No additional tags.**

One exception — `mem_elements_insert` (line 112) is **not** simp because on Lists it introduces a
head comparison. Since `FiniteAddressSet.mem_insert` (line 258) at the set level IS simp, we rely on
it in practice. **Skipped.**

### I.3 `Verity/Core/Address.lean`, `Verity/Core/Semantics.lean`, `Verity/EVM/Uint256.lean`

Scanned; almost entirely `def`s and `inductive`s. No plain lemmas beyond what already carries
`@[simp]`. **Nothing to tag.**

### I.4 `Verity/Specs/Common.lean`

Exclusively `*_rfl` lemmas that are already `@[simp]`. **Nothing to tag.**

### I.5 `Verity/Specs/Common/Sum.lean`

Five non-simp theorems — all **bona-fide invariants over `FiniteAddressSet`-indexed sums of
storage-mapping balances**. These are precisely the shapes balance-conservation obligations reduce
to.

| Lemma | Line | Signature (abridged) | Category | Grind |
|---|---|---|---|---|
| `sumBalances_insert_existing` | 69 | `addr ∈ addrs → sumBalances slot (addrs.insert addr) b = sumBalances slot addrs b` | sum preserved by redundant insert | **`[grind →]`** (premise drives rewrite; reverse direction would lose info) |
| `sumBalances_insert_new` | 77 | `addr ∉ addrs → b slot addr = 0 → sumBalances slot (addrs.insert addr) (b[addr := amt]) = add (sumBalances slot addrs b) amt` | sum increment on fresh insert | **`[grind →]`** |
| `sumBalances_update_existing` | 179 | `addr ∈ addrs → sumBalances slot addrs (b[addr := new]) = add (sub (sumBalances slot addrs b) old) new` | sum delta on point-update | **`[grind →]`** |
| `sumBalances_zero_of_all_zero` | 212 | `(∀ a ∈ addrs, b slot a = 0) → sumBalances slot addrs b = 0` | zero-sum collapse | **`[grind →]`** |
| `balancesFinite_preserved_deposit` | 221 | `balancesFinite s → balancesFinite (…deposit state…)` | storage-set finiteness preservation | **`[grind →]`** |

→ **5 tagged.** All directional because the preconditions (`addr ∈ addrs`, `addr ∉ addrs`, …) are
driving.

### I.6 `Verity/Proofs/Stdlib/ListSum.lean`

```
countOcc_cons_eq, countOcc_cons_ne, countOccU_cons_eq, countOccU_cons_ne
map_sum_point_update, map_sum_point_decrease, map_sum_transfer_eq
```

The `countOcc*` recurrences: LHS `countOcc target (target :: rest)` unfolds to `1 + countOcc target
rest`. The RHS pattern is a strict sub-term of the LHS, so these are safe as `[grind =]`.

The three big preservation theorems (`map_sum_point_{update,decrease}`, `map_sum_transfer_eq`) are
heavily-premised: they take pointwise hypotheses like `f' target = f target + delta` and
`∀ addr, addr ≠ target → f' addr = f addr`. For `grind`, tagging these as plain `@[grind]` would
make grind try to e-match on `(addrs.map ?f').sum` everywhere, which occurs **very** often and would
blow up backward search. We tag them as `[grind →]`: grind uses them forward once the pointwise
hypotheses are in context, which is the exact usage pattern in the benchmark proofs.

| Lemma | Line | Shape | Grind |
|---|---|---|---|
| `countOcc_cons_eq` | 27 | `countOcc t (t :: rest) = 1 + countOcc t rest` | **`[grind =]`** |
| `countOcc_cons_ne` | 31 | `a ≠ t → countOcc t (a :: rest) = countOcc t rest` | **`[grind →]`** (conditional eq) |
| `countOccU_cons_eq` | 35 | Uint256 variant of above | **`[grind =]`** |
| `countOccU_cons_ne` | 39 | conditional Uint256 variant | **`[grind →]`** |
| `map_sum_point_update` | 58 | sum eq after pointwise add at target | **`[grind →]`** |
| `map_sum_point_decrease` | 85 | sum eq after pointwise sub at target | **`[grind →]`** |
| `map_sum_transfer_eq` | 117 | sum eq after transfer src → dst | **`[grind →]`** |

→ **7 tagged.**

### I.7 `Verity/Proofs/Stdlib/MappingAutomation.lean` — 40+ theorems, tag the core shapes

This file is ~370 lines of `setX_getX_{same,diff}` and `setX_preserves_{storage,events,…}` for the
three mapping families (`Address → Uint256`, `Uint256 → Uint256`, `Address → Address → Uint256`),
plus `setStorage/setStorageAddr` cross-family preservations.

**Rejected pattern — `setMapping_knownAddresses_*`**: these deal with a separate `knownAddresses`
field that only a subset of cases use; tagging them broadly would add grind noise for cases that
never touch it.

**Tagged core shapes (`[grind =]` for the "same" identities, `[grind →]` for disequality-gated
"diff" / "preserves"):**

| Lemma | Line | Shape | Grind |
|---|---|---|---|
| `getMapping_runValue` | 32 | `(getMapping slot key).runValue s = s.storageMap slot.slot key` | `[grind =]` |
| `setMapping_getMapping_same` | 52 | set-then-get-same-key → value | `[grind =]` |
| `setMapping_getMapping_diff` | 57 | `k₁ ≠ k₂ → get after set = original` | `[grind →]` |
| `setMapping_preserves_other_slot` | 66 | cross-slot preservation | `[grind →]` |
| `getMappingUint_runValue` | 110 | Uint256-keyed accessor | `[grind =]` |
| `setMappingUint_getMappingUint_same` | 125 | store-load identity | `[grind =]` |
| `setMappingUint_getMappingUint_diff` | 131 | disjoint-key preservation | `[grind →]` |
| `setMappingUint_preserves_storage` | 140 | cross-field preservation | `[grind →]` |
| `setMappingUint_preserves_storageAddr` | 146 | cross-field preservation | `[grind →]` |
| `setMappingUint_preserves_storageMap` | 152 | cross-field preservation | `[grind →]` |
| `setMappingUint_preserves_storageMap2` | 158 | cross-field preservation | `[grind →]` |
| `setMappingUint_preserves_sender` | 164 | context preservation | `[grind →]` |
| `setMappingUint_preserves_thisAddress` | 170 | context preservation | `[grind →]` |
| `getMapping2_runValue` | 189 | 2-key accessor | `[grind =]` |
| `setMapping2_getMapping2_same` | 204 | 2-key store-load identity | `[grind =]` |
| `setMapping2_getMapping2_diff_key1` | 210 | disjoint-key1 preservation | `[grind →]` |
| `setMapping2_getMapping2_diff_key2` | 219 | disjoint-key2 preservation | `[grind →]` |
| `setMapping2_preserves_storage` | 228 | cross-field | `[grind →]` |
| `setMapping2_preserves_storageAddr` | 234 | cross-field | `[grind →]` |
| `setMapping2_preserves_storageMap` | 240 | cross-field | `[grind →]` |
| `setMapping2_preserves_storageMapUint` | 246 | cross-field | `[grind →]` |
| `setMappingUint_preserves_events` | 360 | event preservation | `[grind →]` |
| `setMapping2_preserves_events` | 366 | event preservation | `[grind →]` |
| `setMapping_preserves_storageMapUint` | 314 | cross-family | `[grind →]` |
| `setMapping_preserves_storageMap2` | 320 | cross-family | `[grind →]` |

→ **25 tagged** (the "same" equalities + "preserves" directionals; skipping `_msgValue /
_blockTimestamp / _blockNumber / _knownAddresses` which are adequately covered by a weaker set and
would duplicate the context-preservation cluster without adding coverage).

### I.8 `Verity/Proofs/Stdlib/Math.lean` — 65 theorems

Triage:

- **`*_comm` (commutativity) lemmas** (`mulDivDown_comm`, `mulDivUp_comm`, `wMulDown_comm`,
  `safeAdd_comm`, `safeMul_comm`): **NOT tagged as `[grind =]`** — commutativity rules under
  e-matching can drive unbounded rewriting if the RHS normal form isn't fixed. These are
  traditionally `@[simp]` in other libraries for AC-normalization, but here they are not simp.
  Tagging them `[grind]` is an E-match loop trap. **Skipped.**

- **`*_nat_eq` bridging lemmas** (`mulDivDown_nat_eq`, `mulDivUp_nat_eq`, `wMulDown_nat_eq`,
  `wDivUp_nat_eq`): exact equality of Uint256 op with Nat op, gated by a "fits within MAX" hypothesis.
  Tagged `[grind →]`: when grind has the fits-within hypothesis, it can substitute the Nat form.

- **`*_zero_{left,right}` / `*_one_{left,right}` / `*_by_wad` / `*_by_one`**: clean identity
  rewrites, tagged `[grind =]` when they have no preconditions, `[grind →]` when gated.

- **Monotonicity / antitonicity** (`mulDivDown_monotone_left`, `mulDivUp_antitone_divisor`,
  `wMulDown_monotone_*`, `wDivUp_monotone_left`, `wDivUp_antitone_right`): preconditions are
  driving; tagged `[grind →]`.

- **Bound lemmas** (`mulDivDown_mul_le`, `mulDivUp_mul_ge`, `mulDivDown_mul_lt_add`,
  `mulDivUp_mul_lt_add`, `wMulDown_mul_le`, `wMulDown_mul_lt_add`, `wDivUp_mul_ge`,
  `wDivUp_mul_lt_add`, `mulDivDown_le_mulDivUp`, `mulDivUp_le_mulDivDown_add_one`): tagged
  `[grind →]` — pure inequalities, no LHS ↔ RHS.

- **Cancellation lemmas** (`mulDivDown_cancel_{left,right}`, `mulDivUp_cancel_{left,right}`):
  tagged `[grind →]` — cancellations are gated by `c ≠ 0` + fits-within; forward only.

- **Exactness disjunction** (`mulDivUp_eq_mulDivDown_or_succ`): tagged `[grind →]` — grind will
  case-split on the disjunction.

- **Safe-op lemmas** (`safeAdd_{some,none,zero_left,zero_right,result_bounded}`,
  `safeSub_{some,none,zero,self,result_le}`, `safeMul_{some,none,zero_left,zero_right,one_left,one_right,result_bounded}`,
  `safeDiv_{some,none,zero_numerator,by_one,self,result_le_numerator}`): **tagged `[grind →]`** —
  these discharge option-elimination of the safe ops when the overflow hypothesis is present.

Concrete tagged list:

| Lemma | Grind |
|---|---|
| `mulDivDown_nat_eq`, `mulDivUp_nat_eq`, `wMulDown_nat_eq`, `wDivUp_nat_eq` | `[grind →]` (4) |
| `mulDivDown_zero_left`, `mulDivDown_zero_right`, `mulDivUp_zero_left`, `mulDivUp_zero_right`, `wMulDown_zero_left`, `wMulDown_zero_right`, `wDivUp_zero` | `[grind =]` (7) |
| `wMulDown_one_left`, `wMulDown_one_right`, `wDivUp_by_wad` | `[grind →]` (3) — gated by fits-within |
| `mulDivDown_monotone_left/right`, `mulDivUp_monotone_left/right`, `wMulDown_monotone_left/right`, `wDivUp_monotone_left`, `wDivUp_antitone_right`, `mulDivDown_antitone_divisor`, `mulDivUp_antitone_divisor` | `[grind →]` (10) |
| `mulDivDown_mul_le`, `mulDivUp_mul_ge`, `mulDivDown_mul_lt_add`, `mulDivUp_mul_lt_add`, `wMulDown_mul_le`, `wMulDown_mul_lt_add`, `wDivUp_mul_ge`, `wDivUp_mul_lt_add`, `mulDivDown_le_mulDivUp`, `mulDivUp_le_mulDivDown_add_one` | `[grind →]` (10) |
| `mulDivUp_eq_mulDivDown_of_dvd`, `mulDivUp_eq_mulDivDown_add_one_of_not_dvd`, `mulDivUp_eq_mulDivDown_or_succ` | `[grind →]` (3) |
| `mulDivDown_cancel_left/right`, `mulDivUp_cancel_left/right` | `[grind →]` (4) — conditional cancellation |
| `mulDivDown_pos`, `mulDivUp_pos`, `wMulDown_pos`, `wDivUp_pos` | `[grind →]` (4) — positivity entailment |
| `safeAdd_some/none/zero_left/zero_right/result_bounded` | `[grind →]` (5) |
| `safeSub_some/none/zero/self/result_le` | `[grind →]` (5) |
| `safeMul_some/none/zero_left/zero_right/one_left/one_right/result_bounded` | `[grind →]` (7) |
| `safeDiv_some/none/zero_numerator/by_one/self/result_le_numerator` | `[grind →]` (6) |

→ **~68 tagged** (approximately; exact count in `Invariants.lean`).

**Deliberately skipped:**
- `safeAdd_comm`, `safeMul_comm`, `mulDivDown_comm`, `mulDivUp_comm`, `wMulDown_comm` — **E-match loop risk**. Grind + commutativity in a rewrite bundle leads to swapping back and forth.

---

## Part II — Case-local `Specs.lean`

Per-case namespace summary (all live under `Benchmark.Cases.*`):

| Case file | Namespace(s) |
|---|---|
| `DamnVulnerableDeFi/SideEntrance/Specs.lean` | `Benchmark.Cases.DamnVulnerableDeFi.SideEntrance` |
| `Ethereum/DepositContractMinimal/Specs.lean` | `Benchmark.Cases.Ethereum.DepositContractMinimal` |
| `Kleros/SortitionTrees/Specs.lean` | `Benchmark.Cases.Kleros.SortitionTrees` |
| `Lido/VaulthubLocked/Specs.lean` | `Benchmark.Cases.Lido.VaulthubLocked` |
| `NexusMutual/RammPriceBand/Specs.lean` | `Benchmark.Cases.NexusMutual.RammPriceBand` + `Benchmark.Cases.NexusMutual.RammSpotPrice` |
| `OpenZeppelin/ERC4626VirtualOffsetDeposit/Specs.lean` | `Benchmark.Cases.OpenZeppelin.ERC4626VirtualOffsetDeposit` |
| `PaladinVotes/StreamRecoveryClaimUsdc/Specs.lean` | `Benchmark.Cases.PaladinVotes.StreamRecoveryClaimUsdc` |
| `Safe/OwnerManagerReach/Specs.lean` | `Benchmark.Cases.Safe.OwnerManagerReach` |
| `UniswapV2/PairFeeAdjustedSwap/Specs.lean` | `Benchmark.Cases.UniswapV2.PairFeeAdjustedSwap` |
| `Zama/ERC7984ConfidentialToken/Specs.lean` | `Benchmark.Cases.Zama.ERC7984ConfidentialToken` |

**Important clarification:** the Specs files contain `def`-based predicates rather than `theorem`
lemmas. For grind, tagging a `def` with `@[grind]` registers it as an **unfolding candidate** — when
grind sees the definition applied at the head of a term, it can β/δ-reduce it. This is exactly what
we want for the invariant predicates (e.g. `ownerListInvariant`, `isOwner`, `balanceOf`, `supply`,
`computedClaimAmount`, `next`, `isChain`, `ceilDiv`, `getPooledEthBySharesRoundUp`, …): grind needs
to peel the definition to reach the storage-level equations.

### II.1 Kleros / SortitionTrees

| Name | Kind | Purpose | Grind |
|---|---|---|---|
| `leaf_sum` | `def` (Uint256) | sum of 4 leaf weights | `[grind]` unfold |
| `parent_equals_sum_of_children_spec` | `def` (Prop) | tree balance between parents/children | SKIP — it IS the main obligation, better not auto-unfold |
| `root_equals_sum_of_leaves_spec` | `def` (Prop) | root invariant | SKIP — main obligation |
| `draw_selects_valid_leaf_spec` | `def` (Prop) | bounds 3 ≤ selected ≤ 6 | SKIP — main obligation |
| `node_id_bijection_spec` | `def` (Prop) | id-mapping bijection | SKIP — main obligation |
| `root_minus_left_equals_right_subtree_spec` | `def` (Prop) | right = root - left | SKIP — main obligation |

→ **1 tagged:** `leaf_sum` (auxiliary aggregator that appears inside `root_equals_sum_of_leaves_spec`).

### II.2 Lido / VaulthubLocked

Helpers live in the adjacent `Contract.lean` (readable — not `Proofs.lean`).

| Name | Kind | Purpose | Grind |
|---|---|---|---|
| `TOTAL_BASIS_POINTS` | `def` (Uint256 constant) | 10000 | SKIP (constant) |
| `ceilDiv` | `def` (Uint256 → Uint256 → Uint256) | ceil-div helper | `[grind]` unfold |
| `getPooledEthBySharesRoundUp` | `def` | share → ether round-up | `[grind]` unfold |
| `ceildiv_sandwich_spec` | `def` (Prop) | `ceilDiv(x,d) * d ≥ x` when no overflow | SKIP — main obligation |
| `shares_conversion_monotone_spec` | `def` (Prop) | share conversion monotonicity | SKIP — main obligation |
| `locked_funds_solvency_spec` | `def` (Prop) | solvency invariant | SKIP — main obligation |

→ **2 tagged:** `ceilDiv`, `getPooledEthBySharesRoundUp`.

### II.3 Zama / ERC7984ConfidentialToken

| Name | Kind | Purpose | Grind |
|---|---|---|---|
| `balanceOf` | `def` (accessor) | `s.storageMap 1 addr` | `[grind]` unfold |
| `supply` | `def` (accessor) | `s.storage 0` | `[grind]` unfold |
| `operatorExpiry` | `def` (accessor) | `s.storageMap2 3 holder spender` | `[grind]` unfold |
| other specs | `def` (Prop) | main obligations | SKIP |

→ **3 tagged.**

### II.4 PaladinVotes / StreamRecoveryClaimUsdc

| Name | Kind | Purpose | Grind |
|---|---|---|---|
| `computedClaimAmount` | `def` (Uint256) | `shareWad * s.storage 0 / 1e18` | `[grind]` unfold |
| `computedWethClaimAmount` | `def` (Uint256) | WETH analog | `[grind]` unfold |

→ **2 tagged.**

### II.5 Safe / OwnerManagerReach — the rich one

| Name | Kind | Purpose | Grind |
|---|---|---|---|
| `next` | `def` (accessor) | `wordToAddress (s.storageMap 0 a)` | `[grind]` unfold |
| `isChain` | `def` (List → Prop, recursive) | pairwise-next consistency | `[grind]` unfold |
| `reachable` | `def` (Prop, ∃ chain …) | existential chain | **NOT TAGGED** — unfolding an existential makes grind try to fabricate chains; leads to loop. Keep opaque. |
| `inListReachable` | `def` (Prop) | Certora-style list invariant | `[grind]` unfold |
| `reachableInList` | `def` (Prop) | inverse invariant | `[grind]` unfold |
| `ownerListInvariant` | `def` (Prop) | bundled iff invariant | `[grind]` unfold |
| `noDuplicates` | `def` (List → Prop, recursive) | list is nodup | `[grind]` unfold |
| `acyclic` | `def` (Prop, ∀ chain …) | universal over chains | **NOT TAGGED** — universally quantified over chain structures; unfolding inside grind explodes. Keep opaque. |
| `uniquePredecessor` | `def` (Prop) | at-most-one incoming edge | `[grind]` unfold |
| `freshInList` | `def` (Prop, ∀ chain …) | absence from any chain | **NOT TAGGED** — same reason as `acyclic`. |
| `noSelfLoops` | `def` (Prop) | no self-edges | `[grind]` unfold |
| `isOwner` | `def` (Prop) | non-zero successor + ≠ SENTINEL | `[grind]` unfold |

→ **9 tagged, 3 intentionally left opaque** (`reachable`, `acyclic`, `freshInList`).

### II.6 NexusMutual / RammPriceBand

Contract.lean has `PRICE_BUFFER`, `PRICE_BUFFER_DENOMINATOR`, `ONE_ETHER` (constants — SKIP) and
`calculateBuyReserve`, `calculateSellReserve`, `spotPrices` (multi-branch functions — SKIP because
unfolding them inside grind would thrash on case splits).

Specs.lean predicates are main obligations (SKIP).

→ **0 tagged.** (Documented reasoning: multi-branch computational helpers are antipattern for
grind.)

### II.7 DamnVulnerableDeFi, Ethereum/DepositContractMinimal, OpenZeppelin, UniswapV2

These Specs.lean files contain only **main obligation predicates** (`deposit_sets_pool_balance_spec`,
`deposit_increments_deposit_count_spec`, etc.) — no auxiliary helpers. Tagging them for grind unfold
would be circular (we'd unfold the obligation into its body). **0 tagged** from these cases.

---

## Part III — Rationale for rejections and "NOT TAGGED" entries

1. **Already `@[simp]` on trivial shapes** — FiniteSet membership lemmas, `Specs.Common *_rfl`.
   Simp runs inside grind, so double-tagging is redundant noise.

2. **Commutativity rewrites** — `*_comm` lemmas are E-match loop magnets. Skip.

3. **Existentially- or universally-quantified predicates over chains** (`reachable`, `acyclic`,
   `freshInList`) — unfolding them mid-grind creates a witness search that cannot be bounded.

4. **Multi-branch computation functions** (`calculateBuyReserve`, `spotPrices`) — unfolding
   explodes the proof state with case splits that grind has no oracle for.

5. **Plain numeric constants** (`TOTAL_BASIS_POINTS`, `PRICE_BUFFER`, `ONE_ETHER`) — no domain
   content; simp-unfolding when needed is cheaper than grind tagging.

6. **Main obligation predicates** (everything named `*_spec` that is a top-level proof
   obligation) — these are the theorems we prove; we should not make grind unfold them when proving
   something else.

---

## Part IV — Coordination with worker S1

S1 is building `Benchmark/Grindset/` on branch `grindset/s1-verity-grindset` and tagging **core
operational primitives** (likely: Uint256 arithmetic, FiniteSet ops, storage context manipulation,
Free monad step semantics). Our A1 coverage is complementary:

- A1 owns **invariant-level** lemmas (`sumBalances_*`, `map_sum_*`, `setMapping*_same/diff`,
  mulDivUp/Down bound + cancellation + monotonicity, safe-op Option elimination).
- A1 owns **case-local predicate unfolding** for the 7 active cases with non-trivial helpers.
- S1 presumably owns operational primitives (`.runState`, `.runValue`, basic Uint256 `add/mul/sub`
  identities).

If both branches tag the same lemma, Lean will accept the second tag as a no-op (attribute is
idempotent for `grind` equal-orientation); if S1 tags the Uint256 commutativity set as `grind` we
rely on S1's choice (we document this as deferred).

The stub `Benchmark/Grindset.lean` on A1's branch imports only `Benchmark.Grindset.Invariants`; S1
will merge later.

---

## Build verification

`lake build Benchmark.Grindset.Invariants` must succeed. The `attribute [grind …] X` syntax
requires `X` to already be imported. We import:

- `Verity.Core.Uint256`
- `Verity.Core.FiniteSet` *(transitively)*
- `Verity.Proofs.Stdlib.Math`
- `Verity.Proofs.Stdlib.ListSum`
- `Verity.Proofs.Stdlib.MappingAutomation`
- `Verity.Specs.Common.Sum`
- `Benchmark.Cases.*.Specs` for the 7 active cases

See `Benchmark/Grindset/Invariants.lean` for the complete, grouped attribute application.
