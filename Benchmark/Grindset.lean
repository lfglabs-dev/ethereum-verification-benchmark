import Benchmark.Grindset.Attr
import Benchmark.Grindset.Monad
import Benchmark.Grindset.Core
import Benchmark.Grindset.Reach
import Benchmark.Grindset.ArithCore

/-!
# Benchmark.Grindset — umbrella module

Single entry point for the Verity grindset. Downstream proofs can write
`import Benchmark.Grindset` and immediately use `grind` / `simp [grind_norm]`
to discharge slot-write, monad-bind, and spec-unfolding obligations.

Every module here is generic and contract-agnostic: nothing may reference
`Benchmark.Cases.*` (enforced by scripts/check_grindset_generic.py). This is
the same set of modules shipped into every agent workspace, so proofs that
work in the repo work for agents and vice versa.

Contents:
- `Grindset.Attr`: `grind_norm` simp set attribute.
- `Grindset.Monad`: `Verity.bind` / `ContractResult.snd` / `Contract.run`
  normalization, branch distribution, Uint256 order normalization.
- `Grindset.Core`: storage + mapping read-after-write lemmas for every
  `ContractState` mapping family.
- `Grindset.Reach`: parameterized reachability/chain lemma pack and the
  `verity_reach_grind` tactic.
- `Grindset.ArithCore`: Uint256→Nat bridges and ceiling-division lemmas.
-/
