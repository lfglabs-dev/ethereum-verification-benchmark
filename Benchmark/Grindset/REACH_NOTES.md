# Grindset Reach extension — design notes

Worker **A3** (branch `grindset/a3-reach-grind-ext`).

## TL;DR

- **Reach shape in the benchmark is not inductive** — the one case
  that genuinely uses reachability (`Safe/OwnerManagerReach`) encodes
  it as an *existential over a witness list* (`List Address`), not as
  `Relation.ReflTransGen` or a custom `inductive Reach` step closure.
- `Benchmark/Grindset/Reach.lean` ships **both** flavours of closure
  lemmas (inductive `Relation.ReflTransGen` and witness-based
  `Reachable`/`IsChain`) so the extension is future-proof.
- `@[grind]` tagging is **deliberately conservative**: only refl /
  one-step / base facts are tagged. `trans` and `snoc` are not tagged
  globally because they are too productive and cause E-matching to
  explode on innocuous terms like `f (f (f a))`.
- The `verity_reach_grind` macro handles the actual closure
  obligations by `apply`-ing `reachable_preserves_invariant` /
  `reach_preserves_invariant` before handing off to `grind`.

## The four flagged cases, reach-wise

| Case                                              | Reach?                                   |
| ------------------------------------------------- | ---------------------------------------- |
| `Kleros/SortitionTrees`                           | No — sum/storage arithmetic only         |
| `Safe/OwnerManagerReach`                          | **Yes — list-witness `reachable`**       |
| `Lido/VaulthubLocked`                             | No — solvency arithmetic (F-01 / P-VH-*) |
| `PaladinVotes/StreamRecoveryClaimUsdc`            | No — claim-state updates only            |

So only `Safe/OwnerManagerReach` actually benefits from a reach pack.
The other three were presumably flagged by keyword match alone.

## The concrete Reach shape in `Safe/OwnerManagerReach`

From `Benchmark/Cases/Safe/OwnerManagerReach/Specs.lean` (paraphrased):

```lean
-- Linked-list next-pointer reader
def next (s : ContractState) (a : Address) : Address :=
  wordToAddress (s.storageMap 0 a)

-- A list of addresses that walks the linked list correctly
def isChain (s : ContractState) : List Address → Prop
  | [] | [_]           => True
  | a :: b :: rest     => next s a = b ∧ isChain s (b :: rest)

-- Reachability via a witness chain
def reachable (s : ContractState) (a b : Address) : Prop :=
  ∃ chain, chain.head? = some a ∧ chain.getLast? = some b ∧ isChain s chain
```

Key observation: **reach induction here is list induction**, not
inductive-predicate induction. This is a deliberate choice — Certora's
`reach` predicate was replaced with a witness-style existential
because the Safe linked list is naturally finite and the witness is a
first-class object proofs can manipulate.

## What `Reach.lean` provides

### Part 1 — Inductive reach (`Relation.ReflTransGen`)

For future cases that *do* use the inductive formulation (none of the
four flagged cases do, but it's a common pattern). Lemmas tagged
`@[grind]`:

| Lemma                       | Role                                          |
| --------------------------- | --------------------------------------------- |
| `reach_refl`                | `ReflTransGen r a a`                          |
| `reach_of_step`             | single step ⇒ reach                           |
| `reach_tail` / `reach_head` | snoc / cons extension                         |
| `reach_trans`               | transitivity                                  |

Plus an un-tagged closure lemma:

| Lemma                       | Role                                          |
| --------------------------- | --------------------------------------------- |
| `reach_preserves_invariant` | `(∀ x y, r x y → P x → P y) → ∀ a b, R* a b → P a → P b` |

### Part 2 — Witness-based reach (`Reachable` / `IsChain`)

Generic over `σ` (state) and `α` (node). Definitions mirror the Safe
case verbatim. Lemmas:

| Lemma                          | Tagged `@[grind]`? | Role                                   |
| ------------------------------ | ------------------ | -------------------------------------- |
| `isChain_nil`, `isChain_singleton` | yes            | base cases                             |
| `isChain_cons_cons`            | `@[simp]` only     | Iff unfolding (pattern too generic for grind) |
| `isChain_tail`                 | no                 | structural lemma                       |
| `reachable_refl`               | yes                | `Reachable step s a a`                 |
| `reachable_step`               | yes                | `Reachable step s a (step s a)`        |
| `reachable_of_step`            | yes                | alias of `reachable_step`              |
| `reachable_snoc`               | **no** (loops)     | extend reach by one step               |
| `reachable_trans`              | **no** (loops)     | transitivity                           |
| `reachable_preserves_invariant`| no                 | the canonical closure lemma            |

### Part 3 — The `verity_reach_grind` tactic

A macro that:

1. First tries `apply reachable_preserves_invariant <;> grind` — this
   is the canonical shape of nearly every reach-closure obligation.
2. Falls back to `apply reach_preserves_invariant <;> grind` for the
   inductive `ReflTransGen` variant.
3. Falls back to plain `grind` (base facts are already tagged).
4. As a last resort, retries `grind` with `snoc`/`trans` as explicit
   hints (will usually time out — only useful for tiny chains).

## Why trans/snoc are **not** globally `@[grind]`

Empirically, tagging `reachable_trans` and `reachable_snoc` makes
`grind`'s E-matcher produce thousands of spurious instances such as

```
Reachable chainStep f (chainStep f (chainStep f (chainStep f b))) (chainStep f (chainStep f a))
```

because every existing `Reachable …` fact matches their first hypothesis
pattern and every `chainStep _ _` term plausibly matches the step
pattern. The E-matching "maximum rounds" threshold is hit in <1s.

Leaving them as explicit hints (or arguments to
`verity_reach_grind`'s inner `grind`) scopes them to situations where
a manual `apply` has already fixed the relevant endpoints.

## Demo proofs

`Benchmark/Grindset/ReachTests.lean` contains:

1. `demo_reach_preserves_P` — `Relation.ReflTransGen`-style invariant
   preservation, closed by `verity_reach_grind`.
2. `demo_chain_reach_preserves_membership` — the witness-based analogue
   (`Reachable chainStep f a b → a ∈ S → b ∈ S` assuming `S`
   step-closed), also closed by `verity_reach_grind`. This is the
   exact shape used in the Safe case.

Both are authored from the specs + contract side only — no peeking at
`Proofs.lean`.

There is also a concrete three-step chain example using
`reachable_step` + `reachable_trans` to sanity-check composition.

## Applicability estimate

| Case                                   | Helps via this pack?                                    |
| -------------------------------------- | ------------------------------------------------------- |
| `Safe/OwnerManagerReach`               | **Partially.** `reachable_preserves_invariant` closes generic closure obligations (e.g. `reachableInList` propagation), but the *non-trivial* Safe theorems (`inListReachable`, acyclicity, unique predecessor after `addOwner`/`removeOwner`/`swapOwner`) require case-specific reasoning about how `next` is mutated at a handful of specific keys. The pack turns "induction on reach" into one-liner `verity_reach_grind`, but the surrounding `next`-mutation algebra is still the hard part. Estimate: closes ≤ 30–40% of obligations end-to-end. |
| `Kleros/SortitionTrees`                | No — no reach relation. Needs S1's arithmetic grindset. |
| `Lido/VaulthubLocked`                  | No — no reach relation. Needs S1's arithmetic grindset. |
| `PaladinVotes/StreamRecoveryClaimUsdc` | No — no reach relation. Needs S1's arithmetic grindset. |

So exactly **one** of the four cases actually benefits from the reach
pack. The other three were misclassified as reach-heavy.

## Limitations

- The witness-based lemmas are generic over `step : σ → α → α`. Safe's
  `next s a = wordToAddress (s.storageMap 0 a)` fits this shape, but
  any case using a *relational* step (`next s a = b` as an arbitrary
  predicate, not a function) would need a small adapter to bridge to
  `Relation.ReflTransGen`. Not currently needed.
- `verity_reach_grind` will happily spin on goals that are **not**
  reach-closure shaped (plain `grind` will then hit limits); it is not
  a universal solver.
- The E-matching patterns for `reachable_trans`/`reachable_snoc` are
  intentionally omitted — re-adding them as `@[grind →]` would loop.
  If a future need arises, attach an explicit `grind_pattern` tied to
  a unique top-level symbol.
- `isChain_cons_cons` is only `@[simp]`, not `@[grind]` — its pattern
  is too unconstrained for the E-matcher (matches every cons-cons
  expression).

## Open questions for S1

- If the merged grindset adds a general `Verity.Specs`-level
  `Reachable` alias, `Benchmark.Grindset.Reach.Reachable` can be
  re-expressed as a direct `attribute [grind]` re-tag rather than a
  new namespaced definition.
- Worth checking whether mathlib's `Relation.TransGen`/`EqvGen` need
  analogous packs — not currently exercised by any benchmark case.
