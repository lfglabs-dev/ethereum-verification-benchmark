/-
  Benchmark.Grindset.Monad — simp/grind normalization of the Contract monad
  scaffolding.

  The Verity DSL elaborates `verity_contract` function bodies into do-notation
  over the `Contract` monad, which in turn desugars to chains of
  `Verity.bind`/`Verity.pure` wrapped by `Contract.run` and projected through
  `ContractResult.snd` / `ContractResult.fst`.

  We register these identifiers as `@[simp]` (for the dedicated
  `grind_norm` set) and also `@[grind]` / `@[grind =]` so that `grind` can
  unfold / rewrite them on its own. The goal is that typical benchmark task
  obligations of shape

    ((Contract.f arg).run s).snd.storage n = ...

  normalize down to plain record updates over `s`, at which point `grind`
  can finish with the tagged storage/mapping simp-lemmas in `Core.lean`.
-/

import Verity.Core
import Benchmark.Grindset.Attr

namespace Benchmark.Grindset

open Verity

/-!
## `grind_norm` simp set

Unfolds the bind/pure/run scaffolding so that `Contract.run (do …) s`
collapses into nested applications of the underlying `*_run` lemmas.

Downstream tactics can invoke these lemmas via:

```
simp only [grind_norm] at *
```

or implicitly via the `grind` tactic (all rules below are also tagged
`@[grind]`/`@[grind =]`).
-/


/-! ### Bind and pure -/

@[grind_norm, simp]
theorem bind_def {α β : Type} (m : Contract α) (f : α → Contract β) :
    (m >>= f) = Verity.bind m f := rfl

@[grind_norm, simp]
theorem pure_def {α : Type} (a : α) :
    (Pure.pure a : Contract α) = Verity.pure a := rfl

@[grind_norm, simp]
theorem bind_success {α β : Type} (a : α) (s : ContractState)
    (f : α → Contract β) :
    Verity.bind (fun state => ContractResult.success a state) f s =
      f a s := rfl

/-! ### `Contract.run` against constructors -/

@[grind_norm, simp]
theorem Contract_run_success {α : Type} (a : α) (s : ContractState) :
    Contract.run (fun state => ContractResult.success a state) s =
      ContractResult.success a s := rfl

/-! ### Projection-through-constructor lemmas

The two core structural facts used by every spec-unfolding proof: after
reducing the monadic body to a `ContractResult.success a s'`, projecting out
`.snd` gives back `s'`. These are already `@[simp]` upstream, but we re-tag
them for `grind` so the tactic can apply them directly. -/

attribute [grind_norm] ContractResult.snd_success ContractResult.snd_revert
attribute [grind_norm] ContractResult.fst_success
attribute [grind_norm] Contract.bind_pure_left Contract.bind_pure_right
attribute [grind_norm] Contract.bind_assoc

/-! ### Primitive operation `.run` lemmas.

These are `@[simp]` upstream. Re-tagging into `grind_norm` keeps everything
accessible via one attribute when running the normalization pass. -/

attribute [grind_norm] getStorage_run setStorage_run
attribute [grind_norm] getStorageAddr_run setStorageAddr_run
attribute [grind_norm] getMapping_run setMapping_run
attribute [grind_norm] getMapping2_run setMapping2_run
attribute [grind_norm] getMappingUint_run setMappingUint_run
attribute [grind_norm] msgSender_run contractAddress_run msgValue_run
attribute [grind_norm] blockTimestamp_run blockNumber_run chainid_run
attribute [grind_norm] require_true require_false
attribute [grind_norm] pure_run

/-!
### Definitional unfolds

The Verity monadic primitives are ordinary `def`s; we need the simp set to
be able to unfold them so `Verity.bind (setStorage … …) f s` can reduce to
a `ContractResult.success …` pattern that the `*_run` lemmas (and the `.snd`
projection lemmas) can finish. -/

attribute [grind_norm] Verity.bind Verity.pure
attribute [grind_norm] Verity.Contract.run
attribute [grind_norm] Verity.getStorage Verity.setStorage
attribute [grind_norm] Verity.getStorageAddr Verity.setStorageAddr
attribute [grind_norm] Verity.getMapping Verity.setMapping
attribute [grind_norm] Verity.getMapping2 Verity.setMapping2
attribute [grind_norm] Verity.getMappingUint Verity.setMappingUint
attribute [grind_norm] Verity.msgSender Verity.contractAddress
attribute [grind_norm] Verity.msgValue
attribute [grind_norm] Verity.blockTimestamp Verity.blockNumber Verity.chainid
attribute [grind_norm] Verity.require

/-! ### `require` branch discharge

The `verity_contract` macro elaborates `require (a <= b) msg` into
`Verity.require (decide (a ≤ b)) msg`, which after unfolding becomes
`fun s => if decide (a ≤ b) = true then ContractResult.success () s else …`.
A proof-side hypothesis `h : a ≤ b` passed into `simp only […, h]` rewrites
the inner `Prop` to `True`, leaving the residual guard
`if decide True = true then success … else revert …`. The ground
`simp only [grind_norm, …]` simp set does not include a rule that collapses
this guard — without it the enclosing `Verity.bind` / `Contract.run` matches
cannot commit to their success branch and `grind` is handed a large
unreduced term whose storage projection it cannot see through.

The lemma below is the missing rewrite. It discharges the `require` in one
step, unblocking the rest of the monadic normalisation. -/

@[grind_norm, simp]
theorem ite_decide_True {α : Sort _} (a b : α) :
    (if decide True = true then a else b) = a := by
  simp

end Benchmark.Grindset
