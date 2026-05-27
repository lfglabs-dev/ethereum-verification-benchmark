import Verity.Specs.Common
import Mathlib.Logic.Relation
import Mathlib.Data.List.Basic

/-!
# Grindset: Reach closure extension

Custom `grind` attribute pack and a bespoke tactic (`verity_reach_grind`)
for discharging reachability / reach-closure obligations that recur
across several Verity benchmark cases.

## Reach shapes actually found in the benchmark

We inspected the four cases flagged as reachability-heavy. Only one of
them uses a real reach relation; the others turned out to be arithmetic
or ownership specs with no transitive closure:

* `Benchmark/Cases/Safe/OwnerManagerReach` — **does** use reach. The
  shape is *witness-based*, not inductive:

  ```
  def isChain (s : ContractState) : List Address → Prop
    | []           => True
    | [_]          => True
    | a :: b :: t  => next s a = b ∧ isChain s (b :: t)

  def reachable (s : ContractState) (a b : Address) : Prop :=
    ∃ chain, chain.head? = some a
           ∧ chain.getLast? = some b
           ∧ isChain s chain
  ```

* `Benchmark/Cases/Kleros/SortitionTrees` — storage arithmetic
  invariants, no reach relation.
* `Benchmark/Cases/Lido/VaulthubLocked` — solvency arithmetic (F-01),
  no reach relation.
* `Benchmark/Cases/PaladinVotes/StreamRecoveryClaimUsdc` — claim-state
  updates, no reach relation.

Because only `Safe/OwnerManagerReach` is genuinely reach-heavy we focus
on its shape. We *also* provide a generic pack for
`Relation.ReflTransGen` (the standard mathlib inductive transitive
closure) so that future cases that pick the inductive formulation will
be covered out of the box.
-/

set_option linter.unusedSectionVars false

namespace Benchmark.Grindset.Reach

open Verity
open Verity.EVM.Uint256

/-! ## Part 1 — Generic inductive reach via `Relation.ReflTransGen`

`Relation.ReflTransGen r a b` is the reflexive–transitive closure of a
step relation `r : α → α → Prop`. Useful closure lemmas are already
provided by mathlib; we re-export them under `@[grind]` so `grind` can
chain steps and preserve step-wise invariants automatically.
-/

section ReflTransGen
variable {α : Type*} {r : α → α → Prop}

-- Reflexivity is the obvious "no step" base case.
@[grind]
theorem reach_refl (a : α) : Relation.ReflTransGen r a a :=
  Relation.ReflTransGen.refl

-- One step is already reach.
@[grind]
theorem reach_of_step {a b : α} (h : r a b) : Relation.ReflTransGen r a b :=
  Relation.ReflTransGen.single h

-- Snoc: extend a reach by a final step (native mathlib shape).
@[grind]
theorem reach_tail {a b c : α}
    (h₁ : Relation.ReflTransGen r a b) (h₂ : r b c) :
    Relation.ReflTransGen r a c :=
  Relation.ReflTransGen.tail h₁ h₂

-- Cons: prefix a reach by an initial step.
@[grind]
theorem reach_head {a b c : α}
    (h₁ : r a b) (h₂ : Relation.ReflTransGen r b c) :
    Relation.ReflTransGen r a c :=
  Relation.ReflTransGen.head h₁ h₂

-- Transitivity.
@[grind]
theorem reach_trans {a b c : α}
    (h₁ : Relation.ReflTransGen r a b) (h₂ : Relation.ReflTransGen r b c) :
    Relation.ReflTransGen r a c :=
  Relation.ReflTransGen.trans h₁ h₂

/--
Invariant preservation under `ReflTransGen`. If `P` is preserved by
every `r`-step, then `P` is preserved by `ReflTransGen r`.

This is the *canonical* "reach-closure" lemma and the thing `grind`
has the hardest time synthesising on its own, because it hides an
induction on the reach derivation.
-/
theorem reach_preserves_invariant
    {P : α → Prop}
    (hStep : ∀ x y, r x y → P x → P y)
    {a b : α} (hR : Relation.ReflTransGen r a b) (hP : P a) : P b := by
  induction hR with
  | refl => exact hP
  | tail _ hrxy ih => exact hStep _ _ hrxy ih

end ReflTransGen

/-! ## Part 2 — Witness-based reach (`isChain` / `reachable` shape)

This is the shape actually used in `Safe/OwnerManagerReach`. We don't
import that module (we want `Grindset.Reach` to be self-contained and
reusable), so we reproduce the shape generically over a *step function*
`step : σ → α → α` and derive the same closure theorems. A user who
has their own `reachable` and `isChain` can then just plumb through
these lemmas with a one-line adapter.
-/

section ChainReach
variable {σ : Type*} {α : Type*}

/-- A chain is a list where consecutive elements are connected by
`step s`. Mirrors `Safe.OwnerManagerReach.isChain` generically. -/
def IsChain (step : σ → α → α) (s : σ) : List α → Prop
  | []          => True
  | [_]         => True
  | a :: b :: t => step s a = b ∧ IsChain step s (b :: t)

@[grind, simp]
theorem isChain_nil (step : σ → α → α) (s : σ) :
    IsChain step s ([] : List α) := trivial

@[grind, simp]
theorem isChain_singleton (step : σ → α → α) (s : σ) (a : α) :
    IsChain step s [a] := trivial

@[simp]
theorem isChain_cons_cons (step : σ → α → α) (s : σ) (a b : α) (t : List α) :
    IsChain step s (a :: b :: t) ↔
      step s a = b ∧ IsChain step s (b :: t) := Iff.rfl

/-- Tail of a chain is a chain. Useful for inducting over chain length. -/
theorem isChain_tail (step : σ → α → α) (s : σ) :
    ∀ {a : α} {t : List α}, IsChain step s (a :: t) → IsChain step s t
  | _, [], _ => trivial
  | _, _ :: _, h => h.2

/-- Append a `step s b` tail to a chain ending at `b`. -/
private theorem isChain_append_step (step : σ → α → α) (s : σ) (b : α) :
    ∀ (chain : List α),
      IsChain step s chain → chain.getLast? = some b →
      IsChain step s (chain ++ [step s b])
  | [], _, h => by simp [List.getLast?] at h
  | [a], _, hlast => by
      have ha : a = b := by simpa [List.getLast?] using hlast
      subst ha
      exact ⟨rfl, trivial⟩
  | a₁ :: a₂ :: t, hch, hlast => by
      have hstep : step s a₁ = a₂ := hch.1
      have hrest : IsChain step s (a₂ :: t) := hch.2
      have hlast' : (a₂ :: t).getLast? = some b := by
        simpa [List.getLast?] using hlast
      have ih := isChain_append_step step s b (a₂ :: t) hrest hlast'
      -- (a₁ :: a₂ :: t) ++ [step s b] = a₁ :: ((a₂ :: t) ++ [step s b])
      show IsChain step s (a₁ :: ((a₂ :: t) ++ [step s b]))
      exact ⟨hstep, ih⟩

/-- Witness-based reachability: there is a chain from `a` to `b`. -/
def Reachable (step : σ → α → α) (s : σ) (a b : α) : Prop :=
  ∃ chain : List α,
    chain.head? = some a ∧
    chain.getLast? = some b ∧
    IsChain step s chain

theorem reachable_refl (step : σ → α → α) (s : σ) (a : α) :
    Reachable step s a a :=
  ⟨[a], rfl, rfl, isChain_singleton step s a⟩

theorem reachable_step (step : σ → α → α) (s : σ) (a : α) :
    Reachable step s a (step s a) :=
  ⟨[a, step s a], rfl, rfl, ⟨rfl, trivial⟩⟩

/--
A single forward step preserves reachability: if `Reachable s a b`
then `Reachable s a (step s b)`. This is the most common closure
lemma in practice (the Safe proofs repeatedly extend a witnessed
chain by one hop).
-/
theorem reachable_snoc (step : σ → α → α) (s : σ)
    {a b : α} (h : Reachable step s a b) :
    Reachable step s a (step s b) := by
  obtain ⟨chain, hhd, hlast, hch⟩ := h
  refine ⟨chain ++ [step s b], ?_, ?_, ?_⟩
  · -- head of chain ++ [x] is head of chain when chain ≠ []
    cases chain with
    | nil => simp [List.head?] at hhd
    | cons c cs => simpa [List.head?] using hhd
  · -- last of chain ++ [x] is x
    simp
  · exact isChain_append_step step s b chain hch hlast

/-- Transitivity of chain-reachability (concatenation of witnesses). -/
theorem reachable_trans (step : σ → α → α) (s : σ)
    {a b c : α} (h1 : Reachable step s a b) (h2 : Reachable step s b c) :
    Reachable step s a c := by
  obtain ⟨chain₂, hhd₂, hlast₂, hch₂⟩ := h2
  -- Auxiliary: walk `chain₂` and repeatedly extend the prefix reach
  -- witness by `reachable_snoc`.
  suffices aux : ∀ (chain : List α) (a b c : α),
      chain.head? = some b → chain.getLast? = some c →
      IsChain step s chain → Reachable step s a b → Reachable step s a c from
    aux chain₂ a b c hhd₂ hlast₂ hch₂ h1
  intro chain
  induction chain with
  | nil =>
      intros _ _ _ hhd _ _ _
      simp [List.head?] at hhd
  | cons x xs ih =>
      intros a b c hhd hlast hch h1
      have hx : x = b := by simpa [List.head?] using hhd
      cases xs with
      | nil =>
          have hxc : x = c := by simpa [List.getLast?] using hlast
          have hbc : b = c := hx ▸ hxc
          exact hbc ▸ h1
      | cons y ys =>
          have hstep : step s x = y := hch.1
          have hrest : IsChain step s (y :: ys) := hch.2
          have hlast' : (y :: ys).getLast? = some c := by
            simpa [List.getLast?] using hlast
          have hhd' : (y :: ys).head? = some y := rfl
          have hstep_b : step s b = y := hx ▸ hstep
          have hay : Reachable step s a y := by
            have := reachable_snoc step s h1
            rw [hstep_b] at this
            exact this
          exact ih a y c hhd' hlast' hrest hay

/--
**The** reach-closure lemma for the chain-witness shape:
an invariant preserved by every `step` is preserved by `Reachable`.

This is the `reach_preserves_invariant` counterpart for witness-based
reach — see `REACH_NOTES.md` for discussion.
-/
theorem reachable_preserves_invariant
    {step : σ → α → α} {s : σ} {P : α → Prop}
    (hStep : ∀ x, P x → P (step s x))
    {a b : α} (h : Reachable step s a b) (hP : P a) : P b := by
  obtain ⟨chain, hhd, hlast, hch⟩ := h
  -- Auxiliary: for any chain with head = some a, last = some b, and
  -- `IsChain`, `P a → P b`. Proven by induction on the chain.
  suffices aux : ∀ (chain : List α) (a b : α),
      chain.head? = some a → chain.getLast? = some b →
      IsChain step s chain → P a → P b from aux chain a b hhd hlast hch hP
  intro chain
  induction chain with
  | nil =>
      intros a b hhd _ _ _
      simp [List.head?] at hhd
  | cons x xs ih =>
      intros a b hhd hlast hch hP
      have hx : x = a := by simpa [List.head?] using hhd
      cases xs with
      | nil =>
          have hxb : x = b := by simpa [List.getLast?] using hlast
          have hab : a = b := hx ▸ hxb
          exact hab ▸ hP
      | cons y ys =>
          have hstep : step s x = y := hch.1
          have hrest : IsChain step s (y :: ys) := hch.2
          have hlast' : (y :: ys).getLast? = some b := by
            simpa [List.getLast?] using hlast
          have hhd' : (y :: ys).head? = some y := rfl
          have hstep_a : step s a = y := hx ▸ hstep
          have hPy : P y := hstep_a ▸ hStep a hP
          exact ih y b hhd' hlast' hrest hPy

/-- Convenience: if reaching `a` from itself then extending by a step,
we land exactly at `step s a`. Useful sugar for `grind`. -/
theorem reachable_of_step (step : σ → α → α) (s : σ) (a : α) :
    Reachable step s a (step s a) := reachable_step step s a

end ChainReach

-- We intentionally do NOT tag `reachable_snoc` or `reachable_trans`
-- globally with `@[grind]` — they are too productive (each instance
-- fires on any reachability fact in context and can loop the
-- E-matcher). They are still handed to `grind` as explicit hints
-- inside the `verity_reach_grind` macro in controlled situations.
attribute [grind] reachable_refl
attribute [grind] reachable_step
attribute [grind] reachable_of_step

/-! ## Part 3 — The `verity_reach_grind` tactic

`grind`'s E-matcher is strong at rewriting and propagating equalities,
but it cannot synthesise inductions on reach derivations on its own.
The lemmas above ship the induction *result* as ordinary theorems, so
most concrete obligations of the form

  `Reachable step s a b → Inv a → Inv b`

close via `reachable_preserves_invariant` plus `grind`'s usual
unfolding. For trickier goals we expose a tactic macro that tries a
plain `grind` first, then falls back to applying the closure lemmas
before re-invoking `grind`.

We deliberately use a simple `macro` (not parameterised by extra
`grind` hints) — extra hypotheses can always be introduced by the user
before calling `verity_reach_grind` and `grind` will pick them up.
-/

/--
`verity_reach_grind` is a small wrapper over `grind` that makes the
standard reach-closure lemmas available as hints. If the direct
`grind` attempt fails, it tries `reachable_preserves_invariant` /
`reach_preserves_invariant` and re-runs `grind` in each subgoal.
-/
macro (name := verity_reach_grind) "verity_reach_grind" : tactic =>
  `(tactic|
    first
    -- 1. Try the canonical reach-preservation closure first. This
    --    handles the overwhelmingly common "Reach … → Inv … → Inv …"
    --    shape by applying `*_preserves_invariant` and dispatching
    --    the step-preservation subgoal by `grind`.
    | (apply Benchmark.Grindset.Reach.reachable_preserves_invariant <;>
        first | assumption | grind)
    | (apply Benchmark.Grindset.Reach.reach_preserves_invariant <;>
        first | assumption | grind)
    -- 2. Plain `grind` (no snoc/trans, to avoid E-matcher loops). The
    --    cheap closure facts (`refl`, `step`, `of_step`) are already
    --    globally tagged `@[grind]` and will fire automatically.
    | grind
    -- 3. Last-ditch: include the productive lemmas explicitly. Only
    --    useful for tiny finite chains; usually hits thresholds.
    | grind [reach_trans, reach_tail, reach_head,
             reachable_snoc, reachable_trans])

end Benchmark.Grindset.Reach
