import Benchmark.Grindset.Reach
import Mathlib.Logic.Relation

/-!
# Grindset: Reach closure — demo proofs

These two tests demonstrate that the `Reach.lean` extension really
does close reach-closure obligations. They are *independent* of any
case's `Proofs.lean` — both theorems are authored from scratch using
only the specs side (an abstract `step` / `next` function and a
user-supplied step-preservation hypothesis).

Both tests are closed using `verity_reach_grind`, the macro defined in
`Benchmark.Grindset.Reach`.
-/

set_option linter.unusedSectionVars false

namespace Benchmark.Grindset.Reach.Tests

open Benchmark.Grindset.Reach

/-! ## Demo 1 — inductive `ReflTransGen` invariant preservation

A small linked-list style state: the state is a function `Nat → Nat`
mapping each slot to the "next" slot. The step relation says `a` can
step to `b` in state `f` iff `f a = b`. We prove that any invariant
which is preserved by one step is preserved under the full transitive
closure — the standard "reach-preserves-invariant" shape.

This closes via the generic `ReflTransGen`-tagged lemmas.
-/

def stepRel (f : Nat → Nat) (a b : Nat) : Prop := f a = b

/--
If `P` is closed under `stepRel f` then `P` is closed under
`Relation.ReflTransGen (stepRel f)`. Closed by `verity_reach_grind`.
-/
theorem demo_reach_preserves_P
    (f : Nat → Nat) (P : Nat → Prop)
    (hStep : ∀ x, P x → P (f x))
    (a b : Nat) (hR : Relation.ReflTransGen (stepRel f) a b) (hPa : P a) :
    P b := by
  have hStep' : ∀ x y, stepRel f x y → P x → P y := by
    intro x y hxy hPx
    -- stepRel f x y unfolds to f x = y
    have : f x = y := hxy
    exact this ▸ hStep x hPx
  -- Our macro tries plain grind first, then the closure lemma.
  verity_reach_grind

/-! ## Demo 2 — chain-witness reach preserves a set-membership invariant

Here we mirror the exact shape used in `Safe/OwnerManagerReach`: a
witnessed chain `Reachable step s a b`, a state-dependent step
function, and an invariant (membership in a step-closed set) that must
propagate along the chain.

The proof is closed using `verity_reach_grind`, which invokes
`reachable_preserves_invariant` under the hood.
-/

/--
State type: a function from `Nat` (a node) to its successor. The step
function is just state application.
-/
def chainStep (f : Nat → Nat) (a : Nat) : Nat := f a

/--
If a set `S` is closed under `chainStep f` (i.e. `x ∈ S → f x ∈ S`)
and `Reachable (chainStep) f a b` holds, then `a ∈ S → b ∈ S`.

This is the *exact* reach-closure obligation pattern from the Safe
OwnerManagerReach specs (once one specialises `σ := ContractState`,
`α := Address`, `chainStep := next`, and takes `S` to be any
`next`-closed address set such as "nodes reachable from SENTINEL").
-/
theorem demo_chain_reach_preserves_membership
    (f : Nat → Nat) (S : Set Nat)
    (hClosed : ∀ x, x ∈ S → f x ∈ S)
    (a b : Nat) (hR : Reachable chainStep f a b) (hA : a ∈ S) :
    b ∈ S := by
  -- `chainStep f x = f x` by definition, so membership-closure under
  -- `f` is exactly membership-closure under `chainStep`.
  have hStep : ∀ x, x ∈ S → chainStep f x ∈ S := hClosed
  verity_reach_grind

/-! ## Sanity: the closure lemmas also let `grind` chain concrete steps -/

/-- Three-step chain: builds a reach by stacking `reachable_step`. -/
example (f : Nat → Nat) (a : Nat) :
    Reachable chainStep f a (f (f (f a))) := by
  -- Each `reachable_step` gives one hop; the trans lemma chains them.
  have h1 : Reachable chainStep f a (f a) := reachable_step chainStep f a
  have h2 : Reachable chainStep f (f a) (f (f a)) :=
    reachable_step chainStep f (f a)
  have h3 : Reachable chainStep f (f (f a)) (f (f (f a))) :=
    reachable_step chainStep f (f (f a))
  exact reachable_trans chainStep f (reachable_trans chainStep f h1 h2) h3

end Benchmark.Grindset.Reach.Tests
