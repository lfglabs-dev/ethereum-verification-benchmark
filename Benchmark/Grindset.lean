import Benchmark.Grindset.Invariants
import Benchmark.Grindset.Reach
import Benchmark.Grindset.Attr
import Benchmark.Grindset.Monad
import Benchmark.Grindset.Core
import Benchmark.Grindset.Tests
import Benchmark.Grindset.Arith

/-!
# Benchmark.Grindset — umbrella module

Single entry point for the Verity grindset. Downstream proofs can write
`import Benchmark.Grindset` and immediately use `grind` to discharge
slot-write, monad-bind, and spec-unfolding obligations.

Contents:
- `Grindset.Attr` (S1): `grind_norm` simp set attribute.
- `Grindset.Monad` (S1): `Verity.bind` / `ContractResult.snd` / `Contract.run`
  normalization lemmas.
- `Grindset.Core` (S1): storage + mapping operational lemmas.
- `Grindset.Tests` (S1): three demo proofs closed by `grind`.
- `Grindset.Invariants` (A1): 118 `@[grind =] / @[grind →] / @[grind]`
  tagged invariant lemmas across all benchmark contracts.
- `Grindset.Reach` (A3): reachability lemma pack and the
  `verity_reach_grind` tactic for `safe/owner_manager_reach` chain proofs.
- `Grindset.Arith` (A4): arithmetic grind pack for `lido/vaulthub_locked`
  — ceilDiv unfolding, sandwich, monotonicity, Uint256↔Nat wrappers.
-/
